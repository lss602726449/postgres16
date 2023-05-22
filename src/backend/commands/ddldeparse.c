/*-------------------------------------------------------------------------
 *
 * ddldeparse.c
 *	  Functions to convert utility commands to machine-parseable
 *	  representation
 *
 * Portions Copyright (c) 1996-2023, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * NOTES
 *
 * This is intended to provide JSON blobs representing DDL commands, which can
 * later be re-processed into plain strings by well-defined sprintf-like
 * expansion.  These JSON objects are intended to allow for machine-editing of
 * the commands, by replacing certain nodes within the objects.
 *
 * Much of the information in the output blob actually comes from system
 * catalogs, not from the command parse node, as it is impossible to reliably
 * construct a fully-specified command (i.e. one not dependent on search_path
 * etc) looking only at the parse node.
 *
 * Deparsed JsonbValue is created by using:
 * 	new_jsonb_VA where the key-value pairs composing an jsonb object can be
 * 	derived using the passed variable arguments. In order to successfully
 *  construct one key:value pair, a set of three arguments consisting of a name
 * 	(string), type (from the jbvType enum) and value must be supplied. It can
 *  take multiple such sets and construct multiple key-value pairs and append
 *  those to output parse-state.
 *
 * IDENTIFICATION
 *	  src/backend/commands/ddldeparse.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/amapi.h"
#include "access/relation.h"
#include "access/table.h"
#include "catalog/namespace.h"
#include "catalog/pg_collation.h"
#include "catalog/pg_constraint.h"
#include "catalog/pg_depend.h"
#include "catalog/pg_inherits.h"
#include "catalog/pg_namespace.h"
#include "catalog/pg_proc.h"
#include "catalog/pg_type.h"
#include "commands/defrem.h"
#include "commands/sequence.h"
#include "commands/tablespace.h"
#include "commands/tablecmds.h"
#include "funcapi.h"
#include "partitioning/partbounds.h"
#include "tcop/ddldeparse.h"
#include "tcop/utility.h"
#include "utils/builtins.h"
#include "utils/fmgroids.h"
#include "utils/jsonb.h"
#include "utils/lsyscache.h"
#include "utils/rel.h"
#include "utils/ruleutils.h"
#include "utils/syscache.h"

/* Estimated length of the generated jsonb string */
#define JSONB_ESTIMATED_LEN 128

/*
 * Return the string representation of the given RELPERSISTENCE value.
 */
static char *
get_persistence_str(char persistence)
{
	switch (persistence)
	{
		case RELPERSISTENCE_TEMP:
			return "TEMPORARY";
		case RELPERSISTENCE_UNLOGGED:
			return "UNLOGGED";
		case RELPERSISTENCE_PERMANENT:
			return NULL;
		default:
			elog(ERROR, "unexpected persistence marking %c",
				 persistence);
			return NULL;		/* make compiler happy */
	}
}

/*
 * Insert JsonbValue key to the output parse state.
 */
static void
insert_jsonb_key(JsonbParseState *state, char *name)
{
	JsonbValue	key;

	/* Push the key */
	key.type = jbvString;
	key.val.string.val = name;
	key.val.string.len = strlen(name);
	pushJsonbValue(&state, WJB_KEY, &key);
}

/*
 * Append new jsonb key:value pairs to the output parse state -- varargs
 * function
 *
 * Arguments:
 * "state": the output jsonb state where each key-value pair is pushed.
 *
 * "numobjs": the number of key:value pairs to be pushed to JsonbParseState;
 * for each one, a name (string), type (from the jbvType enum) and value must
 * be supplied.  The value must match the type given; for instance, jbvBool
 * requires an bool, jbvString requires a char * and so on.
 * Each element type must match the conversion specifier given in the format
 * string, as described in ddl_deparse_expand_command.
 *
 * Notes:
 * a) The caller can pass "fmt":"fmtstr" as a regular key:value pair to this,
 * no special handling needed for that.
 * b) The caller need to carefully pass sets of arguments, we don't have the
 * luxury of sprintf-like compiler warnings for malformed argument lists.
 */
static void
new_jsonb_VA(JsonbParseState *state, int numobjs,...)
{
	va_list		args;
	int			i;
	JsonbValue	val;

	/* Process the given varargs */
	va_start(args, numobjs);

	for (i = 0; i < numobjs; i++)
	{
		char	   *name;
		enum jbvType type;

		name = va_arg(args, char *);
		type = va_arg(args, enum jbvType);

		/* Push the key first */
		insert_jsonb_key(state, name);

		/*
		 * For all param types other than jbvNull, there must be a value in
		 * the varargs. Fetch it and add the fully formed subobject into the
		 * main object.
		 */
		switch (type)
		{
			case jbvNull:
				/* Null params don't have a value (obviously) */
				val.type = jbvNull;
				pushJsonbValue(&state, WJB_VALUE, &val);
				break;

			case jbvBool:
				/* Push the bool value */
				val.type = jbvBool;
				val.val.boolean = va_arg(args, int);
				pushJsonbValue(&state, WJB_VALUE, &val);
				break;

			case jbvString:
				/* Push the string value */
				val.type = jbvString;
				val.val.string.val = pstrdup(va_arg(args, char *));
				val.val.string.len = strlen(val.val.string.val);
				pushJsonbValue(&state, WJB_VALUE, &val);
				break;

			case jbvNumeric:
				/* Push the numeric value */
				val.type = jbvNumeric;
				val.val.numeric = (Numeric)
					DatumGetNumeric(DirectFunctionCall1(
														int8_numeric,
														va_arg(args, int)));

				pushJsonbValue(&state, WJB_VALUE, &val);
				break;

			default:
				elog(ERROR, "unrecognized jbvType %d", type);
		}
	}

	va_end(args);
}

/*
 * A helper routine to insert jsonb for typId to the output parse state.
 */
static void
new_jsonb_for_type(JsonbParseState *state, char *parentKey,
				   Oid typId, int32 typmod)
{
	Oid			typnspid;
	char	   *type_nsp;
	char	   *type_name = NULL;
	char	   *typmodstr;
	bool		type_array;

	Assert(parentKey);

	format_type_detailed(typId, typmod, &typnspid, &type_name, &typmodstr,
						 &type_array);

	if (OidIsValid(typnspid))
		type_nsp = get_namespace_name_or_temp(typnspid);
	else
		type_nsp = pstrdup("");

	insert_jsonb_key(state, parentKey);
	pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);
	new_jsonb_VA(state, 4,
				 "schemaname", jbvString, type_nsp,
				 "typename", jbvString, type_name,
				 "typmod", jbvString, typmodstr,
				 "typarray", jbvBool, type_array);
	pushJsonbValue(&state, WJB_END_OBJECT, NULL);
}

/*
 * A helper routine to set up name: schemaname, objname
 *
 * Elements "schema_name" and "obj_name" are set.  If the namespace OID
 * corresponds to a temp schema, that's set to "pg_temp".
 *
 * The difference between those two element types is whether the obj_name will
 * be quoted as an identifier or not, which is not something that this routine
 * concerns itself with; that will be up to the expand function.
 */
static void
new_jsonb_for_qualname(JsonbParseState *state, Oid nspid, char *objName,
					   char *keyName, bool createObject)
{
	char	   *namespace;

	if (isAnyTempNamespace(nspid))
		namespace = pstrdup("pg_temp");
	else
		namespace = get_namespace_name(nspid);

	/* Push the key first */
	if (keyName)
		insert_jsonb_key(state, keyName);

	if (createObject)
		pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);

	new_jsonb_VA(state, 2,
				 "schemaname", jbvString, namespace,
				 "objname", jbvString, objName);

	if (createObject)
		pushJsonbValue(&state, WJB_END_OBJECT, NULL);
}

/*
 * A helper routine to set up name: 'schemaname, objname' where the object is
 * specified by classId and objId.
 */
static void
new_jsonb_for_qualname_id(JsonbParseState *state, Oid classId, Oid objectId,
						  char *keyName, bool createObject)
{
	Relation	catalog;
	HeapTuple	catobj;
	Datum		obj_nsp;
	Datum		obj_name;
	AttrNumber	Anum_name;
	AttrNumber	Anum_namespace;
	AttrNumber	Anum_oid = get_object_attnum_oid(classId);
	bool		isnull;

	catalog = table_open(classId, AccessShareLock);

	catobj = get_catalog_object_by_oid(catalog, Anum_oid, objectId);
	if (!catobj)
		elog(ERROR, "cache lookup failed for object with OID %u of catalog \"%s\"",
			 objectId, RelationGetRelationName(catalog));
	Anum_name = get_object_attnum_name(classId);
	Anum_namespace = get_object_attnum_namespace(classId);

	obj_nsp = heap_getattr(catobj, Anum_namespace, RelationGetDescr(catalog),
						   &isnull);
	if (isnull)
		elog(ERROR, "null namespace for object %u", objectId);

	obj_name = heap_getattr(catobj, Anum_name, RelationGetDescr(catalog),
							&isnull);
	if (isnull)
		elog(ERROR, "null attribute name for object %u", objectId);

	new_jsonb_for_qualname(state, DatumGetObjectId(obj_nsp),
						   NameStr(*DatumGetName(obj_name)),
						   keyName, createObject);
	table_close(catalog, AccessShareLock);
}

/*
 * A helper routine to insert key:value where value is array of qualname to
 * the output parse state.
 */
static void
new_jsonbArray_for_qualname_id(JsonbParseState *state,
							   char *keyname, List *array)
{
	ListCell   *lc;

	/* Push the key first */
	insert_jsonb_key(state, keyname);

	pushJsonbValue(&state, WJB_BEGIN_ARRAY, NULL);

	/* Push the array elements now */
	foreach(lc, array)
		new_jsonb_for_qualname_id(state, RelationRelationId, lfirst_oid(lc),
								  NULL, true);

	pushJsonbValue(&state, WJB_END_ARRAY, NULL);
}

/*
 * A helper routine to insert collate object for column
 * definition to the output parse state.
 */
static void
insert_collate_object(JsonbParseState *state, char *parentKey, char *fmt,
					  Oid classId, Oid objectId, char *key)
{
	/*
	 * Insert parent key for which we are going to create value object here.
	 */
	if (parentKey)
		insert_jsonb_key(state, parentKey);

	pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);

	new_jsonb_VA(state, 1, "fmt", jbvString, fmt);

	/* push object now */
	new_jsonb_for_qualname_id(state, classId, objectId, key, true);

	pushJsonbValue(&state, WJB_END_OBJECT, NULL);
}

/*
 * A helper routine to insert identity object for the table definition
 * to the output parse state.
 */
static void
insert_identity_object(JsonbParseState *state, Oid nspid, char *relname)
{
	new_jsonb_for_qualname(state, nspid, relname, "identity", true);
}

/*
 * Deparse the sequence CACHE option to Jsonb
 *
 * Verbose syntax
 * CACHE %{value}
 */
static inline void
deparse_Seq_Cache(JsonbParseState *state, Form_pg_sequence seqdata)
{
	pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);
	new_jsonb_VA(state, 3,
				 "fmt", jbvString, "CACHE %{value}s",
				 "clause", jbvString, "cache",
				 "value", jbvString,
				 psprintf(INT64_FORMAT, seqdata->seqcache));
	pushJsonbValue(&state, WJB_END_OBJECT, NULL);
}

/*
 * Deparse the sequence CYCLE option to Jsonb.
 *
 * Verbose syntax
 * %{no}s CYCLE
 */
static inline void
deparse_Seq_Cycle(JsonbParseState *state, Form_pg_sequence seqdata)
{
	StringInfoData fmtStr;

	initStringInfo(&fmtStr);

	pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);

	if (!seqdata->seqcycle)
	{
		appendStringInfoString(&fmtStr, "%{no}s ");
		new_jsonb_VA(state, 1, "no", jbvString, "NO");
	}

	appendStringInfoString(&fmtStr, "CYCLE");
	new_jsonb_VA(state, 2,
				 "fmt", jbvString, fmtStr.data,
				 "clause", jbvString, "cycle");

	pfree(fmtStr.data);
	pushJsonbValue(&state, WJB_END_OBJECT, NULL);
}

/*
 * Deparse the sequence INCREMENT BY option to Jsonb
 *
 * Verbose syntax
 * INCREMENT BY %{value}s
 */
static inline void
deparse_Seq_IncrementBy(JsonbParseState *state, Form_pg_sequence seqdata)
{
	pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);
	new_jsonb_VA(state, 3,
				 "fmt", jbvString, "INCREMENT BY %{value}s",
				 "clause", jbvString, "seqincrement",
				 "value", jbvString,
				 psprintf(INT64_FORMAT, seqdata->seqincrement));
	pushJsonbValue(&state, WJB_END_OBJECT, NULL);
}

/*
 * Deparse the sequence MAXVALUE option to Jsonb.
 *
 * Verbose syntax
 * MAXVALUE %{value}s
 */
static inline void
deparse_Seq_Maxvalue(JsonbParseState *state, Form_pg_sequence seqdata)
{
	pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);
	new_jsonb_VA(state, 3,
				 "fmt", jbvString, "MAXVALUE %{value}s",
				 "clause", jbvString, "maxvalue",
				 "value", jbvString,
				 psprintf(INT64_FORMAT, seqdata->seqmax));
	pushJsonbValue(&state, WJB_END_OBJECT, NULL);
}

/*
 * Deparse the sequence MINVALUE option to Jsonb
 *
 * Verbose syntax
 * MINVALUE %{value}s
 */
static inline void
deparse_Seq_Minvalue(JsonbParseState *state, Form_pg_sequence seqdata)
{
	pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);
	new_jsonb_VA(state, 3,
				 "fmt", jbvString, "MINVALUE %{value}s",
				 "clause", jbvString, "minvalue",
				 "value", jbvString,
				 psprintf(INT64_FORMAT, seqdata->seqmin));
	pushJsonbValue(&state, WJB_END_OBJECT, NULL);
}

/*
 * Deparse the sequence OWNED BY command.
 *
 * Verbose syntax
 * OWNED BY %{owner}D
 */
static void
deparse_Seq_OwnedBy(JsonbParseState *state, Oid sequenceId)
{
	Relation	depRel;
	SysScanDesc scan;
	ScanKeyData keys[3];
	HeapTuple	tuple;
	bool		elem_found PG_USED_FOR_ASSERTS_ONLY = false;

	depRel = table_open(DependRelationId, AccessShareLock);
	ScanKeyInit(&keys[0],
				Anum_pg_depend_classid,
				BTEqualStrategyNumber, F_OIDEQ,
				ObjectIdGetDatum(RelationRelationId));
	ScanKeyInit(&keys[1],
				Anum_pg_depend_objid,
				BTEqualStrategyNumber, F_OIDEQ,
				ObjectIdGetDatum(sequenceId));
	ScanKeyInit(&keys[2],
				Anum_pg_depend_objsubid,
				BTEqualStrategyNumber, F_INT4EQ,
				Int32GetDatum(0));

	scan = systable_beginscan(depRel, DependDependerIndexId, true,
							  NULL, 3, keys);
	while (HeapTupleIsValid(tuple = systable_getnext(scan)))
	{
		Oid			ownerId;
		Form_pg_depend depform;
		char	   *colname;

		depform = (Form_pg_depend) GETSTRUCT(tuple);

		/* Only consider AUTO dependencies on pg_class */
		if (depform->deptype != DEPENDENCY_AUTO)
			continue;
		if (depform->refclassid != RelationRelationId)
			continue;
		if (depform->refobjsubid <= 0)
			continue;

		ownerId = depform->refobjid;
		colname = get_attname(ownerId, depform->refobjsubid, false);

		/* mark the begin of owner's definition object */
		pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);

		new_jsonb_VA(state, 2,
					 "fmt", jbvString, "OWNED BY %{owner}D",
					 "clause", jbvString, "owned");

		/* owner key */
		insert_jsonb_key(state, "owner");

		/* owner value begin */
		pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);

		new_jsonb_for_qualname_id(state, RelationRelationId,
								  ownerId, NULL, false);
		new_jsonb_VA(state, 1, "attrname", jbvString, colname);

		/* owner value end */
		pushJsonbValue(&state, WJB_END_OBJECT, NULL);

		/* mark the end of owner's definition object */
		pushJsonbValue(&state, WJB_END_OBJECT, NULL);

#ifdef USE_ASSERT_CHECKING
		elem_found = true;
#endif
	}

	systable_endscan(scan);
	relation_close(depRel, AccessShareLock);

	/*
	 * If there's no owner column, assert. The caller must have checked
	 * presence of owned_by element before invoking this.
	 */
	Assert(elem_found);
}

/*
 * Deparse the sequence START WITH option to Jsonb.
 *
 * Verbose syntax
 * START WITH %{value}s
 */
static inline void
deparse_Seq_Startwith(JsonbParseState *state, Form_pg_sequence seqdata)
{
	pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);
	new_jsonb_VA(state, 3,
				 "fmt", jbvString, "START WITH %{value}s",
				 "clause", jbvString, "start",
				 "value", jbvString,
				 psprintf(INT64_FORMAT, seqdata->seqstart));
	pushJsonbValue(&state, WJB_END_OBJECT, NULL);
}

/*
 * Deparse the sequence RESTART option to Jsonb
 *
 * Verbose syntax
 * RESTART %{value}s
 */
static inline void
deparse_Seq_Restart(JsonbParseState *state, int64 last_value)
{
	pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);
	new_jsonb_VA(state, 3,
				 "fmt", jbvString, "RESTART %{value}s",
				 "clause", jbvString, "restart",
				 "value", jbvString,
				 psprintf(INT64_FORMAT, last_value));
	pushJsonbValue(&state, WJB_END_OBJECT, NULL);
}

/*
 * Deparse the sequence AS option.
 *
 * Verbose syntax
 * AS %{seqtype}T
 */
static inline void
deparse_Seq_As(JsonbParseState *state, Form_pg_sequence seqdata)
{
	pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);
	new_jsonb_VA(state, 1, "fmt", jbvString, "AS %{seqtype}T");
	new_jsonb_for_type(state, "seqtype", seqdata->seqtypid, -1);
	pushJsonbValue(&state, WJB_END_OBJECT, NULL);
}

/*
 * Deparse the definition of column identity to Jsonb.
 *
 * Verbose syntax
 * %{identity_type}s ( %{seq_definition: }s )
 * where identity_type is: "GENERATED %{option}s AS IDENTITY"
 */
static void
deparse_ColumnIdentity(JsonbParseState *state, char *parentKey,
					   Oid seqrelid, char identity)
{
	Form_pg_sequence seqform;
	Sequence_values *seqvalues;
	StringInfoData fmtStr;

	initStringInfo(&fmtStr);

	/*
	 * Insert parent key for which we are going to create value object here.
	 */
	if (parentKey)
		insert_jsonb_key(state, parentKey);

	/* create object now for value of identity_column */
	pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);

	/* identity_type object creation */
	if (identity == ATTRIBUTE_IDENTITY_ALWAYS ||
		identity == ATTRIBUTE_IDENTITY_BY_DEFAULT)
	{
		appendStringInfoString(&fmtStr, "%{identity_type}s");
		insert_jsonb_key(state, "identity_type");

		pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);

		new_jsonb_VA(state, 2,
					 "fmt", jbvString,
					 "GENERATED %{option}s AS IDENTITY",
					 "option", jbvString,
					 (identity == ATTRIBUTE_IDENTITY_ALWAYS ?
					  "ALWAYS" : "BY DEFAULT"));
		pushJsonbValue(&state, WJB_END_OBJECT, NULL);
	}

	/* seq_definition array object creation */
	insert_jsonb_key(state, "seq_definition");

	appendStringInfoString(&fmtStr, " ( %{seq_definition: }s )");

	pushJsonbValue(&state, WJB_BEGIN_ARRAY, NULL);

	seqvalues = get_sequence_values(seqrelid);
	seqform = seqvalues->seqform;

	/* Definition elements */
	deparse_Seq_Cache(state, seqform);
	deparse_Seq_Cycle(state, seqform);
	deparse_Seq_IncrementBy(state, seqform);
	deparse_Seq_Minvalue(state, seqform);
	deparse_Seq_Maxvalue(state, seqform);
	deparse_Seq_Startwith(state, seqform);
	deparse_Seq_Restart(state, seqvalues->last_value);
	/* We purposefully do not emit OWNED BY here */

	pushJsonbValue(&state, WJB_END_ARRAY, NULL);

	/* We have full fmt by now, so add jsonb element for that */
	new_jsonb_VA(state, 1, "fmt", jbvString, fmtStr.data);

	pfree(fmtStr.data);

	/* end of idendity_column object */
	pushJsonbValue(&state, WJB_END_OBJECT, NULL);
}

/*
 * Deparse a ColumnDef node within a regular (non-typed) table creation.
 *
 * NOT NULL constraints in the column definition are emitted directly in the
 * column definition by this routine; other constraints must be emitted
 * elsewhere (the info in the parse node is incomplete anyway).
 *
 * Verbose syntax
 * "%{name}I %{coltype}T STORAGE %{colstorage}s %{compression}s %{collation}s
 *  %{not_null}s %{default}s %{identity_column}s %{generated_column}s"
 */
static void
deparse_ColumnDef(JsonbParseState *state, Relation relation,
				  List *dpcontext, bool composite, ColumnDef *coldef)
{
	Oid			relid = RelationGetRelid(relation);
	HeapTuple	attrTup;
	Form_pg_attribute attrForm;
	Oid			typid;
	int32		typmod;
	Oid			typcollation;
	bool		saw_notnull;
	ListCell   *cell;
	StringInfoData fmtStr;

	initStringInfo(&fmtStr);

	/*
	 * Inherited columns without local definitions should be skipped. We don't
	 * want those to be part of final string.
	 */
	if (!coldef->is_local)
		return;

	attrTup = SearchSysCacheAttName(relid, coldef->colname);
	if (!HeapTupleIsValid(attrTup))
		elog(ERROR, "could not find cache entry for column \"%s\" of relation %u",
			 coldef->colname, relid);
	attrForm = (Form_pg_attribute) GETSTRUCT(attrTup);

	get_atttypetypmodcoll(relid, attrForm->attnum,
						  &typid, &typmod, &typcollation);

	/* start making column object */
	pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);

	/* create name and type elements for column */
	appendStringInfoString(&fmtStr, "%{name}I");
	new_jsonb_VA(state, 2,
				 "name", jbvString, coldef->colname,
				 "type", jbvString, "column");

	/*
	 * create coltype object having 4 elements: schemaname, typename, typemod,
	 * typearray
	 */
	appendStringInfoString(&fmtStr, " %{coltype}T");
	new_jsonb_for_type(state, "coltype", typid, typmod);

	/* STORAGE clause */
	if (!composite)
	{
		appendStringInfoString(&fmtStr, " STORAGE %{colstorage}s");
		new_jsonb_VA(state, 1,
					 "colstorage", jbvString,
					 storage_name(attrForm->attstorage));
	}

	/* COMPRESSION clause */
	if (coldef->compression)
	{
		appendStringInfoString(&fmtStr, " %{compression}s");
		insert_jsonb_key(state, "compression");
		pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);
		new_jsonb_VA(state, 2,
					 "fmt", jbvString, "COMPRESSION %{compression_method}I",
					 "compression_method", jbvString, coldef->compression);
		pushJsonbValue(&state, WJB_END_OBJECT, NULL);
	}

	/* COLLATE clause */
	if (OidIsValid(typcollation))
	{
		appendStringInfoString(&fmtStr, " %{collation}s");
		insert_collate_object(state, "collation",
							  "COLLATE %{collation_name}D",
							  CollationRelationId, typcollation,
							  "collation_name");
	}

	if (!composite)
	{
		Oid			seqrelid = InvalidOid;

		/*
		 * Emit a NOT NULL declaration if necessary.  Note that we cannot
		 * trust pg_attribute.attnotnull here, because that bit is also set
		 * when primary keys are specified; we must not emit a NOT NULL
		 * constraint in that case, unless explicitly specified.  Therefore,
		 * we scan the list of constraints attached to this column to
		 * determine whether we need to emit anything. (Fortunately, NOT NULL
		 * constraints cannot be table constraints.)
		 *
		 * In the ALTER TABLE cases, we also add a NOT NULL if the colDef is
		 * marked is_not_null.
		 */
		saw_notnull = false;
		foreach(cell, coldef->constraints)
		{
			Constraint *constr = (Constraint *) lfirst(cell);

			if (constr->contype == CONSTR_NOTNULL)
			{
				saw_notnull = true;
				break;
			}
		}

		/* NOT NULL */
		if (saw_notnull)
		{
			appendStringInfoString(&fmtStr, " %{not_null}s");
			new_jsonb_VA(state, 1,
						 "not_null", jbvString, "NOT NULL");
		}


		/* DEFAULT */
		if (attrForm->atthasdef &&
			coldef->generated != ATTRIBUTE_GENERATED_STORED)
		{
			char	   *defstr;

			appendStringInfoString(&fmtStr, " %{default}s");

			defstr = relation_get_column_default(relation, attrForm->attnum,
												 dpcontext);

			insert_jsonb_key(state, "default");
			pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);
			new_jsonb_VA(state, 2,
						 "fmt", jbvString, "DEFAULT %{default}s",
						 "default", jbvString, defstr);

			pushJsonbValue(&state, WJB_END_OBJECT, NULL);
		}

		/* IDENTITY COLUMN */
		if (coldef->identity)
		{
			/*
			 * For identity column, find the sequence owned by column in order
			 * to deparse the column definition.
			 */
			seqrelid = getIdentitySequence(relid, attrForm->attnum, true);
			if (OidIsValid(seqrelid) && coldef->identitySequence)
				seqrelid = RangeVarGetRelid(coldef->identitySequence,
											NoLock, false);

			if (OidIsValid(seqrelid))
			{
				appendStringInfoString(&fmtStr, " %{identity_column}s");
				deparse_ColumnIdentity(state, "identity_column",
									   seqrelid,
									   coldef->identity);
			}
		}


		/* GENERATED COLUMN EXPRESSION */
		if (coldef->generated == ATTRIBUTE_GENERATED_STORED)
		{
			char	   *defstr;

			appendStringInfoString(&fmtStr, " %{generated_column}s");
			defstr = relation_get_column_default(relation, attrForm->attnum,
												 dpcontext);

			insert_jsonb_key(state, "generated_column");
			pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);
			new_jsonb_VA(state, 2,
						 "fmt", jbvString, "GENERATED ALWAYS AS"
						 " (%{generation_expr}s) STORED",
						 "generation_expr", jbvString, defstr);

			pushJsonbValue(&state, WJB_END_OBJECT, NULL);
		}
	}

	ReleaseSysCache(attrTup);

	/* We have full fmt by now, so add jsonb element for that */
	new_jsonb_VA(state, 1, "fmt", jbvString, fmtStr.data);

	pfree(fmtStr.data);

	/* mark the end of one column object */
	pushJsonbValue(&state, WJB_END_OBJECT, NULL);
}

/*
 * Helper for deparse_ColumnDef_typed()
 *
 * Returns true if we need to deparse a ColumnDef node within a typed
 * table creation.
 */
static bool
deparse_ColDef_typed_needed(Relation relation, ColumnDef *coldef,
							Form_pg_attribute *atFormOut, bool *notnull)
{
	Oid			relid = RelationGetRelid(relation);
	HeapTuple	attrTup;
	Form_pg_attribute attrForm;
	Oid			typid;
	int32		typmod;
	Oid			typcollation;
	bool		saw_notnull;
	ListCell   *cell;

	attrTup = SearchSysCacheAttName(relid, coldef->colname);
	if (!HeapTupleIsValid(attrTup))
		elog(ERROR, "could not find cache entry for column \"%s\" of relation %u",
			 coldef->colname, relid);

	attrForm = (Form_pg_attribute) GETSTRUCT(attrTup);

	if (atFormOut)
		*atFormOut = attrForm;

	get_atttypetypmodcoll(relid, attrForm->attnum,
						  &typid, &typmod, &typcollation);

	/*
	 * Search for a NOT NULL declaration. As in deparse_ColumnDef, we rely on
	 * finding a constraint on the column rather than coldef->is_not_null.
	 * (This routine is never used for ALTER cases.)
	 */
	saw_notnull = false;
	foreach(cell, coldef->constraints)
	{
		Constraint *constr = (Constraint *) lfirst(cell);

		if (constr->contype == CONSTR_NOTNULL)
		{
			saw_notnull = true;
			break;
		}
	}

	if (notnull)
		*notnull = saw_notnull;

	if (!saw_notnull && !attrForm->atthasdef)
	{
		ReleaseSysCache(attrTup);
		return false;
	}

	ReleaseSysCache(attrTup);
	return true;
}

/*
 * Deparse a ColumnDef node within a typed table creation. This is simpler
 * than the regular case, because we don't have to emit the type declaration,
 * collation, or default. Here we only return something if the column is being
 * declared NOT NULL.
 *
 * As in deparse_ColumnDef, any other constraint is processed elsewhere.
 *
 * Verbose syntax
 * %{name}I WITH OPTIONS %{not_null}s %{default}s.
 */
static void
deparse_ColumnDef_typed(JsonbParseState *state, Relation relation,
						List *dpcontext, ColumnDef *coldef)
{
	bool		needed;
	Form_pg_attribute attrForm;
	bool		saw_notnull;
	StringInfoData fmtStr;

	initStringInfo(&fmtStr);

	needed = deparse_ColDef_typed_needed(relation, coldef,
										 &attrForm, &saw_notnull);
	if (!needed)
		return;

	/* start making column object */
	pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);

	appendStringInfoString(&fmtStr, "%{name}I WITH OPTIONS");

	/* TYPE and NAME */
	new_jsonb_VA(state, 2,
				 "type", jbvString, "column",
				 "name", jbvString, coldef->colname);

	/* NOT NULL */
	if (saw_notnull)
	{
		appendStringInfoString(&fmtStr, " %{not_null}s");
		new_jsonb_VA(state, 1, "not_null", jbvString, "NOT NULL");
	}

	/* DEFAULT */
	if (attrForm->atthasdef)
	{
		char	   *defstr;

		appendStringInfoString(&fmtStr, " %{default}s");
		defstr = relation_get_column_default(relation, attrForm->attnum,
											 dpcontext);

		insert_jsonb_key(state, "default");
		pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);
		new_jsonb_VA(state, 2,
					 "fmt", jbvString, "DEFAULT %{default}s",
					 "default", jbvString, defstr);

		pushJsonbValue(&state, WJB_END_OBJECT, NULL);
	}

	/* We have full fmt by now, so add jsonb element for that */
	new_jsonb_VA(state, 1, "fmt", jbvString, fmtStr.data);

	pfree(fmtStr.data);

	/* mark the end of column object */
	pushJsonbValue(&state, WJB_END_OBJECT, NULL);

	/* Generated columns are not supported on typed tables, so we are done */
}

/*
 * Subroutine for CREATE TABLE deparsing.
 *
 * Deal with all the table elements (columns and constraints).
 *
 * Note we ignore constraints in the parse node here; they are extracted from
 * system catalogs instead.
 */
static void
deparse_TableElems(JsonbParseState *state, Relation relation,
				   List *tableElements, List *dpcontext,
				   bool typed, bool composite)
{
	ListCell   *lc;

	foreach(lc, tableElements)
	{
		Node	   *elt = (Node *) lfirst(lc);

		switch (nodeTag(elt))
		{
			case T_ColumnDef:
				{
					if (typed)
						deparse_ColumnDef_typed(state, relation,
												dpcontext,
												(ColumnDef *) elt);
					else
						deparse_ColumnDef(state, relation, dpcontext,
										  composite, (ColumnDef *) elt);
				}
				break;
			case T_Constraint:
				break;
			default:
				elog(ERROR, "invalid node type %d", nodeTag(elt));
		}
	}
}

/*
 * Subroutine for CREATE TABLE deparsing.
 *
 * Given a table OID, obtain its constraints and append them to the given
 * JsonbParseState.
 *
 * This works for typed tables, regular tables.
 *
 * Note that CONSTRAINT_FOREIGN constraints are always ignored.
 */
static void
deparse_Constraints(JsonbParseState *state, Oid relationId)
{
	Relation	conRel;
	ScanKeyData key;
	SysScanDesc scan;
	HeapTuple	tuple;

	Assert(OidIsValid(relationId));

	/*
	 * Scan pg_constraint to fetch all constraints linked to the given
	 * relation.
	 */
	conRel = table_open(ConstraintRelationId, AccessShareLock);
	ScanKeyInit(&key, Anum_pg_constraint_conrelid, BTEqualStrategyNumber,
				F_OIDEQ, ObjectIdGetDatum(relationId));
	scan = systable_beginscan(conRel, ConstraintRelidTypidNameIndexId, true,
							  NULL, 1, &key);

	/*
	 * For each constraint, add a node to the list of table elements.  In
	 * these nodes we include not only the printable information ("fmt"), but
	 * also separate attributes to indicate the type of constraint, for
	 * automatic processing.
	 */
	while (HeapTupleIsValid(tuple = systable_getnext(scan)))
	{
		Form_pg_constraint constrForm;
		char	   *contype;
		StringInfoData fmtStr;

		constrForm = (Form_pg_constraint) GETSTRUCT(tuple);

		switch (constrForm->contype)
		{
			case CONSTRAINT_CHECK:
				contype = "check";
				break;
			case CONSTRAINT_FOREIGN:
				continue;		/* not here */
			case CONSTRAINT_PRIMARY:
				contype = "primary key";
				break;
			case CONSTRAINT_UNIQUE:
				contype = "unique";
				break;
			case CONSTRAINT_EXCLUSION:
				contype = "exclusion";
				break;
			default:
				elog(ERROR, "unrecognized constraint type");
		}

		/* No need to deparse constraints inherited from parent table. */
		if (OidIsValid(constrForm->conparentid))
			continue;

		/*
		 * "type" and "contype" are not part of the printable output, but are
		 * useful to programmatically distinguish these from columns and among
		 * different constraint types.
		 *
		 * XXX it might be useful to also list the column names in a PK, etc.
		 */
		initStringInfo(&fmtStr);
		appendStringInfoString(&fmtStr, "CONSTRAINT %{name}I %{definition}s");
		pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);

		new_jsonb_VA(state, 4,
					 "type", jbvString, "constraint",
					 "contype", jbvString, contype,
					 "name", jbvString, NameStr(constrForm->conname),
					 "definition", jbvString,
					 pg_get_constraintdef_string(constrForm->oid));

		if (constrForm->conindid &&
			(constrForm->contype == CONSTRAINT_PRIMARY ||
			 constrForm->contype == CONSTRAINT_UNIQUE ||
			 constrForm->contype == CONSTRAINT_EXCLUSION))
		{
			Oid			tblspc = get_rel_tablespace(constrForm->conindid);

			if (OidIsValid(tblspc))
			{
				char	   *tblspcname = get_tablespace_name(tblspc);

				if (!tblspcname)
					elog(ERROR, "cache lookup failed for tablespace %u",
						 tblspc);

				appendStringInfoString(&fmtStr,
									   " USING INDEX TABLESPACE %{tblspc}s");
				new_jsonb_VA(state, 1,
							 "tblspc", jbvString, tblspcname);
			}
		}

		/* We have full fmt by now, so add jsonb element for that */
		new_jsonb_VA(state, 1, "fmt", jbvString, fmtStr.data);

		pfree(fmtStr.data);

		pushJsonbValue(&state, WJB_END_OBJECT, NULL);
	}

	systable_endscan(scan);
	table_close(conRel, AccessShareLock);
}

/*
 * Subroutine for CREATE TABLE deparsing.
 *
 * Insert columns and constraints elements(if any) in output JsonbParseState
 */
static void
add_table_elems(JsonbParseState *state, StringInfo fmtStr,
					   Relation relation, List *tableElts, List *dpcontext,
					   Oid objectId, bool inherit, bool typed, bool composite)
{
	insert_jsonb_key(state, "table_elements");

	pushJsonbValue(&state, WJB_BEGIN_ARRAY, NULL);

	/*
	 * Process table elements: column definitions and constraints. Only the
	 * column definitions are obtained from the parse node itself. To get
	 * constraints we rely on pg_constraint, because the parse node might be
	 * missing some things such as the name of the constraints.
	 */
	deparse_TableElems(state, relation, tableElts, dpcontext,
					   typed,	/* typed table */
					   composite);	/* not composite */

	deparse_Constraints(state, objectId);

	/*
	 * Decide if we need to put '()' around table_elements. It is needed for
	 * below cases:
	 *
	 * a) where actual table-elements are present, eg: create table t1 (a int)
	 *
	 * a) inherit case with no local table-elements present, eg: create table
	 * t1 () inherits (t2)
	 *
	 * OTOH, '()' is not needed for below cases when no table-elements are
	 * present:
	 *
	 * a) 'partition of' case, eg: create table t2 partition of t1
	 *
	 * b) 'of type' case, eg: create table t1 of type1;
	 */
	if ((state->contVal.type == jbvArray) &&
		(inherit || (state->contVal.val.array.nElems > 0)))
	{
		appendStringInfoString(fmtStr, " (%{table_elements:, }s)");
	}
	else
		appendStringInfoString(fmtStr, " %{table_elements:, }s");

	/* end of table_elements array */
	pushJsonbValue(&state, WJB_END_ARRAY, NULL);
}

/*
 * Deparse DefElems, as used by Create Table
 *
 * Verbose syntax
 * %{label}s = %{value}L
 * where label is: %{schema}I %{label}I
 */
static void
deparse_DefElem(JsonbParseState *state, DefElem *elem, bool is_reset)
{
	StringInfoData fmtStr;
	StringInfoData labelfmt;

	initStringInfo(&fmtStr);

	appendStringInfoString(&fmtStr, "%{label}s");
	pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);

	/* LABEL */
	initStringInfo(&labelfmt);

	insert_jsonb_key(state, "label");
	pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);

	if (elem->defnamespace != NULL)
	{
		appendStringInfoString(&labelfmt, "%{schema}I.");
		new_jsonb_VA(state, 1,
					 "schema", jbvString, elem->defnamespace);
	}

	appendStringInfoString(&labelfmt, "%{label}I");
	new_jsonb_VA(state, 2,
				 "label", jbvString, elem->defname,
				 "fmt", jbvString, labelfmt.data);
	pfree(labelfmt.data);

	pushJsonbValue(&state, WJB_END_OBJECT, NULL);

	/* VALUE */
	if (!is_reset)
	{
		appendStringInfoString(&fmtStr, " = %{value}L");
		new_jsonb_VA(state, 1, "value", jbvString,
					 elem->arg ? defGetString(elem) :
					 defGetBoolean(elem) ? "true" : "false");
	}

	new_jsonb_VA(state, 1, "fmt", jbvString, fmtStr.data);
	pfree(fmtStr.data);

	pushJsonbValue(&state, WJB_END_OBJECT, NULL);
}

/*
 * Deparse WITH clause, as used by Create Table.
 *
 * Verbose syntax (formulated in helper function deparse_DefElem)
 * %{label}s = %{value}L
 */
static void
deparse_withObj(JsonbParseState *state, CreateStmt *node)
{
	ListCell   *cell;

	/* WITH */
	insert_jsonb_key(state, "with");
	pushJsonbValue(&state, WJB_BEGIN_ARRAY, NULL);

	/* add elements to array */
	foreach(cell, node->options)
	{
		DefElem    *opt = (DefElem *) lfirst(cell);

		deparse_DefElem(state, opt, false);
	}

	/* with's array end */
	pushJsonbValue(&state, WJB_END_ARRAY, NULL);
}

/*
 * Deparse a CreateStmt (CREATE TABLE).
 *
 * Given a table OID and the parse tree that created it, return JsonbValue
 * representing the creation command.
 *
 * Verbose syntax
 * CREATE %{persistence}s TABLE %{if_not_exists}s %{identity}D [OF
 * %{of_type}T | PARTITION OF %{parent_identity}D] %{table_elements}s
 * %{inherits}s %{partition_bound}s %{partition_by}s %{access_method}s
 * %{with_clause}s %{tablespace}s
 */
static Jsonb *
deparse_CreateStmt(Oid objectId, Node *parsetree)
{
	CreateStmt *node = (CreateStmt *) parsetree;
	Relation	relation = relation_open(objectId, AccessShareLock);
	Oid			nspid = relation->rd_rel->relnamespace;
	char	   *relname = RelationGetRelationName(relation);
	List	   *dpcontext;
	char	   *perstr;
	StringInfoData fmtStr;
	JsonbParseState *state = NULL;
	JsonbValue *value;

	initStringInfo(&fmtStr);

	/* mark the begin of ROOT object and start adding elements to it. */
	pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);

	appendStringInfoString(&fmtStr, "CREATE");

	/* PERSISTENCE */
	perstr = get_persistence_str(relation->rd_rel->relpersistence);
	if (perstr)
	{
		appendStringInfoString(&fmtStr, " %{persistence}s");
		new_jsonb_VA(state, 1,
					 "persistence", jbvString, perstr);
	}

	appendStringInfoString(&fmtStr, " TABLE");

	/* IF NOT EXISTS */
	if (node->if_not_exists)
	{
		appendStringInfoString(&fmtStr, " %{if_not_exists}s");
		new_jsonb_VA(state, 1,
					 "if_not_exists", jbvString, "IF NOT EXISTS");
	}

	/* IDENTITY */
	appendStringInfoString(&fmtStr, " %{identity}D");
	insert_identity_object(state, nspid, relname);

	dpcontext = deparse_context_for(RelationGetRelationName(relation),
									objectId);

	/*
	 * TABLE-ELEMENTS array creation
	 */
	if (node->ofTypename || node->partbound)
	{
		/* Insert the "of type" or "partition of" clause whichever present */
		if (node->ofTypename)
		{
			appendStringInfoString(&fmtStr, " OF %{of_type}T");
			new_jsonb_for_type(state, "of_type",
							   relation->rd_rel->reloftype, -1);
		}
		else
		{
			List	   *parents;
			Oid			objid;

			appendStringInfoString(&fmtStr, " PARTITION OF %{parent_identity}D");
			parents = relation_get_inh_parents(objectId);
			objid = linitial_oid(parents);
			Assert(list_length(parents) == 1);
			new_jsonb_for_qualname_id(state, RelationRelationId,
									  objid, "parent_identity", true);
		}

		add_table_elems(state, &fmtStr, relation,
							   node->tableElts, dpcontext, objectId,
							   false,	/* not inherit */
							   true,	/* typed table */
							   false);	/* not composite */
	}
	else
	{
		List	   *inhrelations;

		/*
		 * There is no need to process LIKE clauses separately; they have
		 * already been transformed into columns and constraints.
		 */

		add_table_elems(state, &fmtStr, relation,
							   node->tableElts, dpcontext, objectId,
							   true,	/* inherit */
							   false,	/* not typed table */
							   false);	/* not composite */

		/*
		 * Add inheritance specification.  We cannot simply scan the list of
		 * parents from the parser node, because that may lack the actual
		 * qualified names of the parent relations.  Rather than trying to
		 * re-resolve them from the information in the parse node, it seems
		 * more accurate and convenient to grab it from pg_inherits.
		 */
		if (node->inhRelations != NIL)
		{
			appendStringInfoString(&fmtStr, " %{inherits}s");
			insert_jsonb_key(state, "inherits");

			pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);

			new_jsonb_VA(state, 1, "fmt", jbvString, "INHERITS (%{parents:, }D)");
			inhrelations = relation_get_inh_parents(objectId);

			new_jsonbArray_for_qualname_id(state, "parents", inhrelations);
			pushJsonbValue(&state, WJB_END_OBJECT, NULL);
		}
	}

	/* FOR VALUES clause */
	if (node->partbound)
	{
		appendStringInfoString(&fmtStr, " %{partition_bound}s");

		/*
		 * Get pg_class.relpartbound. We cannot use partbound in the parsetree
		 * directly as it's the original partbound expression which haven't
		 * been transformed.
		 */
		new_jsonb_VA(state, 1,
					 "partition_bound", jbvString,
					 relation_get_part_bound(objectId));
	}

	/* PARTITION BY clause */
	if (relation->rd_rel->relkind == RELKIND_PARTITIONED_TABLE)
	{
		appendStringInfoString(&fmtStr, " %{partition_by}s");
		insert_jsonb_key(state, "partition_by");
		pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);

		new_jsonb_VA(state, 2,
					 "fmt", jbvString, "PARTITION BY %{definition}s",
					 "definition", jbvString,
					 pg_get_partkeydef_string(objectId));

		pushJsonbValue(&state, WJB_END_OBJECT, NULL);
	}

	/* USING clause */
	if (node->accessMethod)
	{
		appendStringInfoString(&fmtStr, " %{access_method}s");
		insert_jsonb_key(state, "access_method");
		pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);

		new_jsonb_VA(state, 2,
					 "fmt", jbvString, "USING %{access_method}I",
					 "access_method", jbvString, node->accessMethod);
		pushJsonbValue(&state, WJB_END_OBJECT, NULL);
	}

	/* WITH clause */
	if (node->options)
	{
		appendStringInfoString(&fmtStr, " %{with_clause}s");
		insert_jsonb_key(state, "with_clause");
		pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);
		new_jsonb_VA(state, 1,
					 "fmt", jbvString, "WITH (%{with:, }s)");

		deparse_withObj(state, node);

		pushJsonbValue(&state, WJB_END_OBJECT, NULL);

	}

	/* TABLESPACE */
	if (node->tablespacename)
	{
		appendStringInfoString(&fmtStr, " %{tablespace}s");
		insert_jsonb_key(state, "tablespace");
		pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);
		new_jsonb_VA(state, 2,
					 "fmt", jbvString, "TABLESPACE %{tablespace}I",
					 "tablespace", jbvString, node->tablespacename);
		pushJsonbValue(&state, WJB_END_OBJECT, NULL);
	}

	relation_close(relation, AccessShareLock);

	/* We have full fmt by now, so add jsonb element for that */
	new_jsonb_VA(state, 1, "fmt", jbvString, fmtStr.data);

	pfree(fmtStr.data);

	/* Mark the end of ROOT object */
	value = pushJsonbValue(&state, WJB_END_OBJECT, NULL);

	return JsonbValueToJsonb(value);
}

/*
 * Deparse a DropStmt (DROP TABLE).
 *
 * Given an object identity and the parse tree that created it, return
 * jsonb string representing the drop command.
 *
 * Verbose syntax
 * DROP TABLE %{concurrently}s %{if_exists}s %{objidentity}s %{cascade}s
 */
char *
deparse_drop_table(const char *objidentity, Node *parsetree)
{
	DropStmt   *node = (DropStmt *) parsetree;
	StringInfoData fmtStr;
	JsonbValue *jsonbval;
	Jsonb	   *jsonb;
	StringInfoData str;
	JsonbParseState *state = NULL;

	initStringInfo(&str);
	initStringInfo(&fmtStr);

	/* mark the begin of ROOT object and start adding elements to it. */
	pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);

	/* Start constructing fmt string */
	appendStringInfoString(&fmtStr, "DROP TABLE");

	/* CONCURRENTLY */
	if (node->concurrent)
	{
		appendStringInfoString(&fmtStr, " %{concurrently}s");
		new_jsonb_VA(state, 1,
					 "concurrently", jbvString, "CONCURRENTLY");
	}

	/* IF EXISTS */
	if (node->missing_ok)
	{
		appendStringInfoString(&fmtStr, " %{if_exists}s");
		new_jsonb_VA(state, 1, "if_exists", jbvString, "IF EXISTS");
	}

	/* IDENTITY */
	appendStringInfoString(&fmtStr, " %{objidentity}s");
	new_jsonb_VA(state, 1, "objidentity", jbvString, objidentity);

	/* CASCADE */
	if (node->behavior == DROP_CASCADE)
	{
		appendStringInfoString(&fmtStr, " %{cascade}s");
		new_jsonb_VA(state, 1, "cascade", jbvString, "CASCADE");
	}

	/* We have full fmt by now, so add jsonb element for that */
	new_jsonb_VA(state, 1, "fmt", jbvString, fmtStr.data);
	pfree(fmtStr.data);

	jsonbval = pushJsonbValue(&state, WJB_END_OBJECT, NULL);

	jsonb = JsonbValueToJsonb(jsonbval);
	return JsonbToCString(&str, &jsonb->root, JSONB_ESTIMATED_LEN);
}

/*
 * Deparse a CreateSeqStmt.
 *
 * Given a sequence OID and the parse tree that created it, return Jsonb
 * representing the creation command.
 *
 * Note: We need to deparse the CREATE SEQUENCE command for the TABLE
 * commands. For example, When creating a table, if we specify a column as a
 * serial type, then we will create a sequence for that column and set that
 * sequence OWNED BY the table. The serial column type information is not
 * available during deparsing phase as that has already been converted to
 * the column default value and sequences creation while parsing.
 *
 * Verbose syntax
 * CREATE %{persistence}s SEQUENCE %{if_not_exists}s %{identity}D %{definition: }s
 */
static Jsonb *
deparse_CreateSeqStmt(Oid objectId, Node *parsetree)
{
	Relation	relation;
	Form_pg_sequence seqform;
	Sequence_values *seqvalues;
	CreateSeqStmt *createSeqStmt = (CreateSeqStmt *) parsetree;
	JsonbParseState *state = NULL;
	JsonbValue *value;
	StringInfoData fmtStr;
	char	   *perstr;

	/*
	 * Only support sequence for IDENTITY COLUMN output separately (via CREATE
	 * TABLE or ALTER TABLE). Otherwise, return empty here.
	 */
	if (createSeqStmt->for_identity)
		return NULL;

	initStringInfo(&fmtStr);
	relation = relation_open(objectId, AccessShareLock);

	/* mark the start of ROOT object */
	pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);
	appendStringInfoString(&fmtStr, "CREATE");

	/* PERSISTENCE */
	perstr = get_persistence_str(relation->rd_rel->relpersistence);
	if (perstr)
	{
		appendStringInfoString(&fmtStr, " %{persistence}s");
		new_jsonb_VA(state, 1,
					 "persistence", jbvString, perstr);
	}

	appendStringInfoString(&fmtStr, " SEQUENCE");

	/* IF NOT EXISTS */
	if (createSeqStmt->if_not_exists)
	{
		appendStringInfoString(&fmtStr, " %{if_not_exists}s");
		new_jsonb_VA(state, 1,
					 "if_not_exists", jbvString, "IF NOT EXISTS");
	}

	/* IDENTITY */
	appendStringInfoString(&fmtStr, " %{identity}D");
	insert_identity_object(state, relation->rd_rel->relnamespace,
						   RelationGetRelationName(relation));

	relation_close(relation, AccessShareLock);

	seqvalues = get_sequence_values(objectId);
	seqform = seqvalues->seqform;

	/* sequence definition array object creation, push the key first */
	appendStringInfoString(&fmtStr, " %{definition: }s");
	insert_jsonb_key(state, "definition");

	pushJsonbValue(&state, WJB_BEGIN_ARRAY, NULL);

	/* Definition elements */
	deparse_Seq_Cache(state, seqform);
	deparse_Seq_Cycle(state, seqform);
	deparse_Seq_IncrementBy(state, seqform);
	deparse_Seq_Minvalue(state, seqform);
	deparse_Seq_Maxvalue(state, seqform);
	deparse_Seq_Startwith(state, seqform);
	deparse_Seq_Restart(state, seqvalues->last_value);
	deparse_Seq_As(state, seqform);
	/* We purposefully do not emit OWNED BY here */

	/* mark the end of sequence definition array */
	pushJsonbValue(&state, WJB_END_ARRAY, NULL);

	/* We have full fmt by now, so add jsonb element for that */
	new_jsonb_VA(state, 1, "fmt", jbvString, fmtStr.data);

	pfree(fmtStr.data);

	/* mark the end of ROOT object */
	value = pushJsonbValue(&state, WJB_END_OBJECT, NULL);

	return JsonbValueToJsonb(value);
}

/*
 * Deparse an AlterSeqStmt.
 *
 * Given a sequence OID and a parse tree that modified it, return Jsonb
 * representing the alter command.
 *
 * Note: We need to deparse the ALTER SEQUENCE command for the TABLE commands.
 * For example, When creating a table, if we specify a column as a serial
 * type, then we will create a sequence for that column and set that sequence
 * OWNED BY the table. The serial column type information is not available
 * during deparsing phase as that has already been converted to the column
 * default value and sequences creation while parsing.
 *
 * Verbose syntax
 * ALTER SEQUENCE %{identity}D %{definition: }s
 */
static Jsonb *
deparse_AlterSeqStmt(Oid objectId, Node *parsetree)
{
	Relation	relation;
	ListCell   *cell;
	Form_pg_sequence seqform;
	Sequence_values *seqvalues;
	AlterSeqStmt *alterSeqStmt = (AlterSeqStmt *) parsetree;
	JsonbParseState *state = NULL;
	JsonbValue *value;

	/*
	 * Sequence for IDENTITY COLUMN output separately (via CREATE TABLE or
	 * ALTER TABLE); return empty here.
	 */
	if (alterSeqStmt->for_identity)
		return NULL;

	relation = relation_open(objectId, AccessShareLock);

	/* mark the start of ROOT object */
	pushJsonbValue(&state, WJB_BEGIN_OBJECT, NULL);

	new_jsonb_VA(state, 1,
				 "fmt", jbvString, "ALTER SEQUENCE %{identity}D %{definition: }s");

	insert_identity_object(state, relation->rd_rel->relnamespace,
						   RelationGetRelationName(relation));
	relation_close(relation, AccessShareLock);

	seqvalues = get_sequence_values(objectId);
	seqform = seqvalues->seqform;

	/* sequence definition array object creation, push the key first */
	insert_jsonb_key(state, "definition");

	/* mark the start of sequence definition array */
	pushJsonbValue(&state, WJB_BEGIN_ARRAY, NULL);

	foreach(cell, ((AlterSeqStmt *) parsetree)->options)
	{
		DefElem    *elem = (DefElem *) lfirst(cell);

		if (strcmp(elem->defname, "cache") == 0)
			deparse_Seq_Cache(state, seqform);
		else if (strcmp(elem->defname, "cycle") == 0)
			deparse_Seq_Cycle(state, seqform);
		else if (strcmp(elem->defname, "increment") == 0)
			deparse_Seq_IncrementBy(state, seqform);
		else if (strcmp(elem->defname, "minvalue") == 0)
			deparse_Seq_Minvalue(state, seqform);
		else if (strcmp(elem->defname, "maxvalue") == 0)
			deparse_Seq_Maxvalue(state, seqform);
		else if (strcmp(elem->defname, "start") == 0)
			deparse_Seq_Startwith(state, seqform);
		else if (strcmp(elem->defname, "restart") == 0)
			deparse_Seq_Restart(state, seqvalues->last_value);
		else if (strcmp(elem->defname, "owned_by") == 0)
			deparse_Seq_OwnedBy(state, objectId);
		else if (strcmp(elem->defname, "as") == 0)
			deparse_Seq_As(state, seqform);
		else
			elog(ERROR, "invalid sequence option %s", elem->defname);
	}

	/* mark the end of sequence definition array */
	pushJsonbValue(&state, WJB_END_ARRAY, NULL);

	/* mark the end of ROOT object */
	value = pushJsonbValue(&state, WJB_END_OBJECT, NULL);

	return JsonbValueToJsonb(value);
}

/*
 * Handle deparsing of simple commands.
 *
 * This function should cover all cases handled in ProcessUtilitySlow.
 */
static Jsonb *
deparse_simple_command(CollectedCommand *cmd)
{
	Oid			objectId;
	Node	   *parsetree;

	Assert(cmd->type == SCT_Simple);

	parsetree = cmd->parsetree;
	objectId = cmd->d.simple.address.objectId;

	if (cmd->in_extension && (nodeTag(parsetree) != T_CreateExtensionStmt))
		return NULL;

	/* This switch needs to handle everything that ProcessUtilitySlow does */
	switch (nodeTag(parsetree))
	{
		case T_AlterSeqStmt:
			return deparse_AlterSeqStmt(objectId, parsetree);

		case T_CreateSeqStmt:
			return deparse_CreateSeqStmt(objectId, parsetree);

		case T_CreateStmt:
			return deparse_CreateStmt(objectId, parsetree);

		default:
			elog(LOG, "unrecognized node type in deparse command: %d",
				 (int) nodeTag(parsetree));
	}

	return NULL;
}

/*
 * Workhorse to deparse a CollectedCommand.
 */
char *
deparse_utility_command(CollectedCommand *cmd)
{
	OverrideSearchPath *overridePath;
	MemoryContext oldcxt;
	MemoryContext tmpcxt;
	char	   *command = NULL;
	StringInfoData str;
	Jsonb	   *jsonb;

	/*
	 * Allocate everything done by the deparsing routines into a temp context,
	 * to avoid having to sprinkle them with memory handling code, but
	 * allocate the output StringInfo before switching.
	 */
	initStringInfo(&str);
	tmpcxt = AllocSetContextCreate(CurrentMemoryContext,
								   "deparse ctx",
								   ALLOCSET_DEFAULT_MINSIZE,
								   ALLOCSET_DEFAULT_INITSIZE,
								   ALLOCSET_DEFAULT_MAXSIZE);
	oldcxt = MemoryContextSwitchTo(tmpcxt);

	/*
	 * Many routines underlying this one will invoke ruleutils.c functionality
	 * to obtain deparsed versions of expressions.  In such results, we want
	 * all object names to be qualified, so that results are "portable" to
	 * environments with different search_path settings.  Rather than
	 * injecting what would be repetitive calls to override search path all
	 * over the place, we do it centrally here.
	 */
	overridePath = GetOverrideSearchPath(CurrentMemoryContext);
	overridePath->schemas = NIL;
	overridePath->addCatalog = false;
	overridePath->addTemp = true;
	PushOverrideSearchPath(overridePath);

	switch (cmd->type)
	{
		case SCT_Simple:
			jsonb = deparse_simple_command(cmd);
			break;
		default:
			elog(ERROR, "unexpected deparse node type %d", cmd->type);
	}

	PopOverrideSearchPath();

	if (jsonb)
		command = JsonbToCString(&str, &jsonb->root, JSONB_ESTIMATED_LEN);

	/*
	 * Clean up.  Note that since we created the StringInfo in the caller's
	 * context, the output string is not deleted here.
	 */
	MemoryContextSwitchTo(oldcxt);
	MemoryContextDelete(tmpcxt);

	return command;
}

/*
 * Given a CollectedCommand, return a JSON representation of it.
 *
 * The command is expanded fully so that there are no ambiguities even in the
 * face of search_path changes.
 */
Datum
ddl_deparse_to_json(PG_FUNCTION_ARGS)
{
	CollectedCommand *cmd = (CollectedCommand *) PG_GETARG_POINTER(0);
	char	   *command;

	command = deparse_utility_command(cmd);

	if (command)
		PG_RETURN_TEXT_P(cstring_to_text(command));

	PG_RETURN_NULL();
}
