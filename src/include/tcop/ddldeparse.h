/*-------------------------------------------------------------------------
 *
 * ddldeparse.h
 *
 * Portions Copyright (c) 2023, PostgreSQL Global Development Group
 *
 * src/include/tcop/ddldeparse.h
 *
 *-------------------------------------------------------------------------
 */
#ifndef DDL_DEPARSE_H
#define DDL_DEPARSE_H

#include "tcop/deparse_utility.h"

/* Context info needed for deparsing ddl command */
typedef struct
{
	/* The maximum volatility of functions in expressions of a DDL command. */
	char		max_volatility;
}			ddl_deparse_context;

extern char *deparse_utility_command(CollectedCommand *cmd,
									 ddl_deparse_context * context);
extern char *deparse_ddl_json_to_string(char *jsonb);
extern char *deparse_drop_table(const char *objidentity, Node *parsetree);

#endif							/* DDL_DEPARSE_H */
