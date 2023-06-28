/*-------------------------------------------------------------------------
 *
 * ddltrigger.c
 *	  Logical DDL triggers.
 *
 * Copyright (c) 2023, PostgreSQL Global Development Group
 *
 * IDENTIFICATION
 *	  src/backend/replication/logical/ddltrigger.c
 *
 * NOTES
 *
 * Deparse the ddl command and log it.
 *
 * ---------------------------------------------------------------------------
 */

#include "postgres.h"

#include "access/table.h"
#include "catalog/pg_class.h"
#include "catalog/pg_proc.h"
#include "commands/event_trigger.h"
#include "funcapi.h"
#include "lib/ilist.h"
#include "replication/ddlmessage.h"
#include "tcop/ddldeparse.h"
#include "utils/fmgrprotos.h"
#include "utils/lsyscache.h"

extern EventTriggerQueryState *currentEventTriggerState;


/*
 * Check if the command can be published.
 *
 * XXX Executing a non-immutable expression during the table rewrite phase is
 * not allowed, as it may result in different data between publisher and
 * subscriber. While some may suggest converting the rewrite inserts to updates
 * and replicate them after the ddl command to maintain data consistency, but it
 * doesn't work if the replica identity column is altered in the command. This
 * is because the rewrite inserts do not contain the old values and therefore
 * cannot be converted to update.
 *
 * Apart from that, commands containing volatile functions are not allowed. Because
 * it's possible the functions contain DDL/DML in which case these operations
 * will be executed twice and cause duplicate data. In addition, we don't know
 * whether the tables being accessed by these DDL/DML are published or not. So
 * blindly allowing such functions can allow unintended clauses like the tables
 * accessed in those functions may not even exist on the subscriber.
 */
static void
check_command_publishable(ddl_deparse_context context, bool is_rewrite)
{

	if (is_rewrite && context.max_volatility != PROVOLATILE_IMMUTABLE)
		ereport(ERROR,
				errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				errmsg("cannot rewrite table if this command contains mutable function because it cannot be replicated in DDL replication"));

	if (context.max_volatility == PROVOLATILE_VOLATILE)
		ereport(ERROR,
				errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				errmsg("cannot use volatile function in this command because it cannot be replicated in DDL replication"));
}

/*
 * Deparse the ddl command and log it prior to
 * execution. Currently only used for DROP TABLE command
 * so that catalog can be accessed before being deleted.
 * This is to check if the table is part of the publication
 * or not.
 */
Datum
publication_deparse_ddl_command_start(PG_FUNCTION_ARGS)
{
	EventTriggerData *trigdata;
	char	   *command = psprintf("Drop table command start");
	DropStmt   *stmt;
	ListCell   *cell1;

	if (!CALLED_AS_EVENT_TRIGGER(fcinfo))
		elog(ERROR, "not fired by event trigger manager");

	trigdata = (EventTriggerData *) fcinfo->context;
	stmt = (DropStmt *) trigdata->parsetree;

	/* Extract the relid from the parse tree */
	foreach(cell1, stmt->objects)
	{
		char		relpersist;
		Node	   *object = lfirst(cell1);
		ObjectAddress address;
		Relation	relation = NULL;

		address = get_object_address(stmt->removeType,
									 object,
									 &relation,
									 AccessExclusiveLock,
									 true);

		/* Object does not exist, nothing to do */
		if (!relation)
			continue;

		relpersist = get_rel_persistence(address.objectId);

		/*
		 * Do not generate wal log for commands whose target table is a
		 * temporary or unlogged table.
		 *
		 * XXX We may generate wal logs for unlogged tables in the future so
		 * that unlogged tables can also be created and altered on the
		 * subscriber side. This makes it possible to directly replay the SET
		 * LOGGED command and the incoming rewrite message without creating a
		 * new table.
		 */
		if (relpersist == RELPERSISTENCE_PERMANENT)
			LogLogicalDDLMessage("deparse", address.objectId, DCT_TableDropStart,
								 command, strlen(command) + 1);

		table_close(relation, NoLock);
	}
	return PointerGetDatum(NULL);
}

/*
 * publication_deparse_table_rewrite
 *
 * Deparse the ddl table rewrite command and log it.
 */
Datum
publication_deparse_table_rewrite(PG_FUNCTION_ARGS)
{
	char		relpersist;
	CollectedCommand *cmd;

	if (!CALLED_AS_EVENT_TRIGGER(fcinfo))
		elog(ERROR, "not fired by event trigger manager");

	cmd = currentEventTriggerState->currentCommand;

	Assert(cmd && cmd->d.alterTable.rewrite);

	relpersist = get_rel_persistence(cmd->d.alterTable.objectId);

	/*
	 * Do not generate wal log for commands whose target table is a temporary
	 * or unlogged table.
	 *
	 * XXX We may generate wal logs for unlogged tables in the future so that
	 * unlogged tables can also be created and altered on the subscriber side.
	 * This makes it possible to directly replay the SET LOGGED command and the
	 * incoming rewrite message without creating a new table.
	 */
	if (relpersist == RELPERSISTENCE_PERMANENT)
	{
		ddl_deparse_context context;
		char	   *json_string;

		/*
		 * Initialize the max_volatility flag to PROVOLATILE_IMMUTABLE, which is
		 * the minimum volatility level.
		 */
		context.max_volatility = PROVOLATILE_IMMUTABLE;

		/* Deparse the DDL command and WAL log it to allow decoding of the same. */
		json_string = deparse_utility_command(cmd, &context);

		if (json_string != NULL)
		{
			check_command_publishable(context, true);
			LogLogicalDDLMessage("deparse", cmd->d.alterTable.objectId, DCT_TableAlter,
								 json_string, strlen(json_string) + 1);
		}
	}

	return PointerGetDatum(NULL);
}

/*
 * Deparse the ddl command and log it. This function
 * is called after the execution of the command but before the
 * transaction commits.
 */
Datum
publication_deparse_ddl_command_end(PG_FUNCTION_ARGS)
{
	ListCell   *lc;
	slist_iter	iter;
	Oid			relid;
	char		relkind;

	if (!CALLED_AS_EVENT_TRIGGER(fcinfo))
		elog(ERROR, "not fired by event trigger manager");

	foreach(lc, currentEventTriggerState->commandList)
	{
		char		relpersist = RELPERSISTENCE_PERMANENT;
		CollectedCommand *cmd = lfirst(lc);
		DeparsedCommandType cmdtype;

		/* Rewrite DDL has been handled in table_rewrite trigger */
		if (cmd->d.alterTable.rewrite)
		{
			RenameStmt *renameStmt = (RenameStmt *) cmd->parsetree;

			if (renameStmt && renameStmt->relationType != OBJECT_TYPE &&
				renameStmt->relationType != OBJECT_TABLE)
				continue;
		}

		if (cmd->type == SCT_Simple &&
			!OidIsValid(cmd->d.simple.address.objectId))
			continue;

		if (cmd->type == SCT_AlterTable)
		{
			relid = cmd->d.alterTable.objectId;
			cmdtype = DCT_TableAlter;
		}
		else
		{
			/* Only SCT_Simple for now */
			relid = cmd->d.simple.address.objectId;
			cmdtype = DCT_SimpleCmd;
		}

		relkind = get_rel_relkind(relid);
		if (relkind)
			relpersist = get_rel_persistence(relid);

		/*
		 * Do not generate wal log for commands whose target table is a
		 * temporary or unlogged table.
		 *
		 * XXX We may generate wal logs for unlogged tables in the future so
		 * that unlogged tables can also be created and altered on the
		 * subscriber side. This makes it possible to directly replay the SET
		 * LOGGED command and the incoming rewrite message without creating a
		 * new table.
		 */
		if (relpersist == RELPERSISTENCE_PERMANENT)
		{
			/*
			 * Deparse the DDL command and WAL log it to allow decoding of the
			 * same.
			 */
			ddl_deparse_context context;
			char	   *json_string;

			/*
			 * Initialize the max_volatility flag to PROVOLATILE_IMMUTABLE, which is
			 * the minimum volatility level.
			 */
			context.max_volatility = PROVOLATILE_IMMUTABLE;

			json_string = deparse_utility_command(cmd, &context);

			if (json_string != NULL)
			{
				check_command_publishable(context, false);
				LogLogicalDDLMessage("deparse", relid, cmdtype, json_string,
									 strlen(json_string) + 1);
			}
		}
	}

	/* Drop commands are not part commandlist but handled here as part of SQLDropList */
	slist_foreach(iter, &(currentEventTriggerState->SQLDropList))
	{
		SQLDropObject *obj;
		EventTriggerData *trigdata;

		trigdata = (EventTriggerData *) fcinfo->context;

		obj = slist_container(SQLDropObject, next, iter.cur);

		if (!obj->original)
			continue;

		if (strcmp(obj->objecttype, "table") == 0)
		{
			DeparsedCommandType cmdtype = DCT_TableDropEnd;
			char	*command;

			command = deparse_drop_table(obj->objidentity, trigdata->parsetree);
			if (command)
				LogLogicalDDLMessage("deparse", obj->address.objectId, cmdtype,
									 command, strlen(command) + 1);
		}
	}

	return PointerGetDatum(NULL);
}

/*
 * publication_deparse_table_init_write
 *
 * Deparse the ddl table create command and log it.
 */
Datum
publication_deparse_table_init_write(PG_FUNCTION_ARGS)
{
	char		relpersist;
	CollectedCommand *cmd;
	ddl_deparse_context context;

	if (!CALLED_AS_EVENT_TRIGGER(fcinfo))
		elog(ERROR, "not fired by event trigger manager");

	cmd = currentEventTriggerState->currentCommand;
	Assert(cmd);

	relpersist = get_rel_persistence(cmd->d.simple.address.objectId);

	/*
	 * Do not generate wal log for commands whose target table is a temporary
	 * table.
	 *
	 * We will generate wal logs for unlogged tables so that unlogged tables
	 * can also be created and altered on the subscriber side. This makes it
	 * possible to directly replay the SET LOGGED command and the incoming
	 * rewrite message without creating a new table.
	 */
	if (relpersist == RELPERSISTENCE_PERMANENT)
	{
		char	   *json_string;

		/*
		 * Initialize the max_volatility flag to PROVOLATILE_IMMUTABLE, which is
		 * the minimum volatility level.
		 */
		context.max_volatility = PROVOLATILE_IMMUTABLE;

		/* Deparse the DDL command and WAL log it to allow decoding of the same. */
		json_string = deparse_utility_command(cmd, &context);

		if (json_string != NULL)
		{
			check_command_publishable(context, false);
			LogLogicalDDLMessage("deparse", cmd->d.simple.address.objectId, DCT_SimpleCmd,
								 json_string, strlen(json_string) + 1);
		}
	}

	return PointerGetDatum(NULL);
}
