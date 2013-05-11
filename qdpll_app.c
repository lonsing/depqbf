/*
 This file is part of DepQBF.

 DepQBF, a solver for quantified boolean formulae (QBF).        
 Copyright 2010, 2011, 2012 Florian Lonsing and Aina Niemetz, Johannes Kepler
 University, Linz, Austria and Vienna University of Technology, Vienna,  Austria.

 DepQBF is free software: you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License, or (at
 your option) any later version.

 DepQBF is distributed in the hope that it will be useful, but
 WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with DepQBF.  If not, see <http://www.gnu.org/licenses/>.
*/


#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <limits.h>
#include <dirent.h>
#include <assert.h>
#include <string.h>
#include <stdarg.h>
#include <signal.h>
#include <unistd.h>
#include <unistd.h>
#include "qdpll.h"
#include "qdpll_internals.h"


#define VERSION						\
  "DepQBF 1.0\n"					\
  "Copyright 2010, 2011, 2012 Florian Lonsing and Aina Niemetz,\n"	\
  "Johannes Kepler University, Linz, Austria and\n"\
"Vienna University of Technology, Vienna, Austria.\n"			\
"This is free software; see COPYING for copying conditions.\n"		\
"There is NO WARRANTY, to the extent permitted by law.\n"



#define USAGE \
"usage: depqbf [ <option> ... ] [ <in-file> ]\n"\
"\n"\
"  where <in-file> is a file in (Q)DIMACS format (default: stdin)\n"\
"  and <option> is any combination of the following:\n"\
"\n"\
"  Note: see function 'qdpll_configure' in file 'qdpll.c' for further, undocumented\n"\
"    options which are not listed here. However, many of those are experimental.\n"\
"\n"\
"  -h, --help                      display usage information\n"\
"  -v                              enable verbosity incrementally (at most '-v -v')\n"\
"  --trace[=<format>]              dump trace in <format> to <stdout>\n"\
"                                    format: qrp  ... ascii QRP format (default)\n"\
"                                            bqrp ... binary QRP format\n"\
"  --qdo                           print variable assignment in QDIMACS output format to <stdout>:\n"\
"                                    if formula is satisfiable, prints a (possibly-partial) satisfying\n"\
"                                    assignment for the outermost existential variables, otherwise prints\n"\
"                                    an assignment for the outermost universal variables\n"\
"  --dep-man=<val>                 set dependency manager: if <val>=qdag (default) then the solver\n"\
"                                    uses the standard dependency scheme; if <val>=simple then the\n"\
"                                    solver uses the given quantifier prefix of the input formula\n"	\
"  --no-cdcl                       disable conflict-driven clause learning and\n"\
"                                    backtrack chronologically from conflicts\n"\
"  --no-sdcl                       disable solution-driven cube learning and\n"\
"                                    backtrack chronologically from solutions\n"\
"  --no-pure-literals              disable pure literal detection\n"\
"  --no-spure-literals             include ALL constraints for pure literal detection (expensive!) \n"\
"  --no-unit-mtf                   no move-to-front (MTF) of learnt constraints which became unit\n"\
"  --no-res-mtf                    no move-to-front (MTF) of learnt constraints which became empty\n"\
"  --max-dec=<val>                 stop after <val> decisions have been made\n"\
"  --lclauses-init-size=<val>      initially allow <val> clauses to be learned before resizing the clause list\n"\
"  --lcubes-init-size=<val>        initially allow <val> cubes to be learned before resizing the cube list\n"\
"  --lclauses-resize-value=<val>   increase capacity of learned clauses list by <val>\n"\
"  --lcubes-resize-value=<val>     increase capacity of learned cubes list by <val>\n"\
"  --orestart-dist-init=<val>      set initial distance of outer restarts to <val> (default 10)\n"\
"  --orestart-dist-inc=<val>       increase distance of outer restarts by <val> (default 5)\n"\
"  --irestart-dist-init=<val>      set initial distance of inner restarts to <val> (default 100)\n"\
"  --irestart-dist-inc=<val>       increase distance of inner restarts by <val> (default 10)\n"\
"\n"





#define QDPLL_ABORT_APP(cond,msg) \
  do {                                  \
    if (cond)                                                                \
      {                                                                        \
        fprintf (stderr, "[QDPLL-APP] %s at line %d: %s\n", __func__,        \
                 __LINE__, msg);                                        \
        fflush (stderr);                                                \
        abort();                                                        \
      }                                                                        \
  } while (0)


struct QDPLLApp
{
  struct
  {
    char *in_filename;
    FILE *in;
    int pretty_print;
    int qdimacs_output;
    int deps_only;
    int print_deps;
    int dump_dep_graph;
    int trace;
    unsigned int max_time;
    unsigned int verbosity;
    unsigned int print_usage;
    unsigned int print_version;
  } options;
};

typedef struct QDPLLApp QDPLLApp;

/* We keep a static pointer to the library object. Currently, this is
   used for calling library functions from within a signal handler. */
static QDPLL *qdpll = 0;

static void
print_abort_err (QDPLLApp * app, char *msg, ...)
{
  va_list list;
  assert (msg != NULL);
  fprintf (stderr, "qdpll-app: ");
  va_start (list, msg);
  vfprintf (stderr, msg, list);
  va_end (list);
  fflush (stderr);
  abort ();
}



/* -------------------- START: PARSING -------------------- */
#define PARSER_READ_NUM(num, c)                        \
  assert (isdigit (c));                                \
  num = 0;					       \
  do						       \
    {						       \
      num = num * 10 + (c - '0');		       \
    }						       \
  while (isdigit ((c = getc (in))));

#define PARSER_SKIP_SPACE_DO_WHILE(c)		     \
  do						     \
    {                                                \
      c = getc (in);				     \
    }                                                \
  while (isspace (c));

#define PARSER_SKIP_SPACE_WHILE(c)		     \
  while (isspace (c))                                \
    c = getc (in);


static void
parse (QDPLLApp * app, QDPLL * qdpll, FILE * in, int trace)
{
  int col = 0, line = 0, neg = 0, preamble_found = 0;
  LitID num = 0;
  QDPLLQuantifierType scope_type = QDPLL_QTYPE_UNDEF;

  assert (in);

  char c;
  while ((c = getc (in)) != EOF)
    {
      PARSER_SKIP_SPACE_WHILE (c);

      while (c == 'c')
        {
          while ((c = getc (in)) != '\n' && c != EOF)
            ;
          c = getc (in);
        }

      PARSER_SKIP_SPACE_WHILE (c);

      if (c == 'p')
        {
          /* parse preamble */
          PARSER_SKIP_SPACE_DO_WHILE (c);
          if (c != 'c')
            goto MALFORMED_PREAMBLE;
          PARSER_SKIP_SPACE_DO_WHILE (c);
          if (c != 'n')
            goto MALFORMED_PREAMBLE;
          PARSER_SKIP_SPACE_DO_WHILE (c);
          if (c != 'f')
            goto MALFORMED_PREAMBLE;
          PARSER_SKIP_SPACE_DO_WHILE (c);
          if (!isdigit (c))
            goto MALFORMED_PREAMBLE;

          /* read number of variables */
          PARSER_READ_NUM (num, c);
          if (trace == TRACE_QRP)
//          fprintf (stdout, "p %s %u", trace == TRACE_QRP ? "qrp" : "bqrp", num);
            fprintf (stdout, "p qrp %u", num);  //TODO
          else if (trace == TRACE_BQRP)
            fprintf (stdout, "p bqrp %u", num); //TODO

          PARSER_SKIP_SPACE_WHILE (c);
          if (!isdigit (c))
            goto MALFORMED_PREAMBLE;

          /* read number of clauses */
          PARSER_READ_NUM (num, c);

          /* NOTE: number of steps is number of orig. clauses, as we can't tell
             the actual, future number of steps when tracing on-the-fly! */
          if (trace)
            fprintf (stdout, " %u%c", num, trace == TRACE_QRP ? '\n' : 0);

          preamble_found = 1;
          goto PARSE_SCOPE_OR_CLAUSE;

        MALFORMED_PREAMBLE:
          QDPLL_ABORT_APP (1, "malformed preamble!\n");
          return;
        }
      else
        {
          QDPLL_ABORT_APP (1, "expecting preamble!\n");
          return;
        }

    PARSE_SCOPE_OR_CLAUSE:

      PARSER_SKIP_SPACE_WHILE (c);

      if (c == 'a' || c == 'e')
        {
          /* open a new scope */
          if (c == 'a')
            scope_type = QDPLL_QTYPE_FORALL;
          else
            scope_type = QDPLL_QTYPE_EXISTS;

          qdpll_new_scope (qdpll, scope_type);

          PARSER_SKIP_SPACE_DO_WHILE (c);
        }

      if (!isdigit (c) && c != '-')
        {
          if (c == EOF)
            return;
          QDPLL_ABORT_APP (1, "expecting digit or '-'!\n");
          return;
        }
      else
        {
          if (c == '-')
            {
              neg = 1;
              if (!isdigit ((c = getc (in))))
                {
                  QDPLL_ABORT_APP (1, "expecting digit!\n");
                  return;
                }
            }

          /* parse a literal or variable ID */
          PARSER_READ_NUM (num, c);
          num = neg ? -num : num;

          qdpll_add (qdpll, num);

          neg = 0;

          goto PARSE_SCOPE_OR_CLAUSE;
        }
    }

  if (!preamble_found)
    QDPLL_ABORT_APP (1, "preamble missing!\n");
}

/* -------------------- END: PARSING -------------------- */



static void
check_options (QDPLLApp * app)
{
  if (app->options.print_deps && !app->options.deps_only)
    print_abort_err (app, "must not use option '%s' without option'%s'!\n\n",
                     "--print-deps", "--deps-only");

  if (app->options.dump_dep_graph && !app->options.deps_only)
    print_abort_err (app, "must not use option '%s' without option'%s'!\n\n",
                     "--dump-dep-graph", "--deps-only");
}


static void
set_default_options (QDPLLApp * app)
{
  app->options.in_filename = 0;
  app->options.in = stdin;
  app->options.pretty_print = 0;
  app->options.deps_only = 0;
  app->options.print_deps = 0;
  app->options.dump_dep_graph = 0;
  app->options.print_usage = 0;
}


static int
isnumstr (char *str)
{
  /* Empty string is not considered as number-string. */
  if (!*str)
    return 0;
  char *p;
  for (p = str; *p; p++)
    {
      if (!isdigit (*p))
        return 0;
    }
  return 1;
}


static void
parse_cmd_line_options (QDPLLApp * app, QDPLL * qdpll, int argc, char **argv)
{
  char *result;
  int opt_cnt;
  for (opt_cnt = 1; opt_cnt < argc; opt_cnt++)
    {
      char *opt_str = argv[opt_cnt];

      if (!strcmp (opt_str, "-h") || !strcmp (opt_str, "--help"))
        {
          app->options.print_usage = 1;
        }
      else if (!strcmp (opt_str, "--version"))
        {
          app->options.print_version = 1;
        }
      else if (!strcmp (opt_str, "--pretty-print"))
        {
          app->options.pretty_print = 1;
        }
      else if (!strcmp (opt_str, "--qdo"))
        {
          app->options.qdimacs_output = 1;
        }
      else if (!strcmp (opt_str, "--deps-only"))
        {
          app->options.deps_only = 1;
        }
      else if (!strcmp (opt_str, "--print-deps"))
        {
          app->options.print_deps = 1;
        }
      else if (!strcmp (opt_str, "--dump-dep-graph"))
        {
          app->options.dump_dep_graph = 1;
        }
      else if (!strcmp (opt_str, "--qdag-print-deps-by-search"))
        {
          app->options.print_deps = 1;
          if ((result = qdpll_configure (qdpll, opt_str)))
            print_abort_err (app, "%s!\n\n", result);
        }
      else if (!strcmp (opt_str, "--trace")
               || !strcmp (opt_str, "--trace=qrp"))
        {
          app->options.trace = TRACE_QRP;
          qdpll_configure (qdpll, opt_str);
        }
      else if (!strcmp (opt_str, "--trace=bqrp"))
        {
          app->options.trace = TRACE_BQRP;
          qdpll_configure (qdpll, opt_str);
        }
      else if (isnumstr (opt_str))
        {
          app->options.max_time = atoi (opt_str);
          if (app->options.max_time == 0)
            {
              result = "Expecting non-zero value for max-time";
              print_abort_err (app, "%s!\n\n", result);
            }
        }
      else if (!strncmp (opt_str, "-", 1) || !strncmp (opt_str, "--", 2))
        {
          /* Handle QDPLL-options. */
          if (!strcmp (opt_str, "-v"))
            {
              app->options.verbosity++;
            }
          if ((result = qdpll_configure (qdpll, opt_str)))
            print_abort_err (app, "%s!\n\n", result);
        }
      else if (!app->options.in_filename)
        {
          app->options.in_filename = opt_str;
          /* Check input file. */
          DIR *dir;
          if ((dir = opendir (app->options.in_filename)) != NULL)
            {
              closedir (dir);
              print_abort_err (app, "input file '%s' is a directory!\n\n",
                               app->options.in_filename);
            }
          FILE *input_file = fopen (app->options.in_filename, "r");
          if (!input_file)
            {
              print_abort_err (app, "could not open input file '%s'!\n\n",
                               app->options.in_filename);
            }
          else
            app->options.in = input_file;
        }
      else
        {
          print_abort_err (app, "unknown option '%s'!\n\n", opt_str);
        }
    }
}


static void
print_deps (QDPLLApp * app, QDPLL * qdpll)
{
  VarID i, max;
  for (i = 1, max = qdpll_get_max_declared_var_id (qdpll); i <= max; i++)
    {
      fprintf (stdout, "%u: ", i);
      qdpll_print_deps (qdpll, i);
      fprintf (stdout, "\n");
    }
  fprintf (stdout, "\n");
}


static void
sig_handler (int sig)
{
  fprintf (stderr, "\n\n SIG RECEIVED\n\n");
#if (COMPUTE_STATS || COMPUTE_TIMES)
  qdpll_print_stats (qdpll);
#endif
  raise (sig);
}


static void
sigalrm_handler (int sig)
{
  fprintf (stderr, "\n\n SIGALRM RECEIVED\n\n");
#if (COMPUTE_STATS || COMPUTE_TIMES)
  qdpll_print_stats (qdpll);
#endif
  raise (sig);
}


static void
set_signal_handlers (QDPLLApp * app)
{
  signal (SIGINT, sig_handler);
  signal (SIGTERM, sig_handler);
  signal (SIGALRM, sigalrm_handler);
}


static void
print_result_message (QDPLLApp * app, QDPLL * qdpll, QDPLLResult result)
{
  /* Print result message; this may not always be desired and depends on the 
     current usage of the solver library. */
  if (!app->options.qdimacs_output)
    {
      /* Print own output format. */
      if (result == QDPLL_RESULT_SAT)
        fprintf (stdout, "SAT\n");
      else if (result == QDPLL_RESULT_UNSAT)
        fprintf (stdout, "UNSAT\n");
      else if (!app->options.pretty_print && !app->options.deps_only)
        {
          assert (result == QDPLL_RESULT_UNKNOWN);
          fprintf (stdout, "UNKNOWN\n");
        }
    }
  else
    {
      /* Print qdimacs-compliant output format. */
      qdpll_print_qdimacs_output (qdpll);
    }
}


static void
print_usage ()
{
  fprintf (stdout, USAGE);
}


static void
print_version ()
{
  fprintf (stderr, VERSION);
}


static void
cleanup (QDPLL * qdpll, QDPLLApp * app)
{
  qdpll_delete (qdpll);

  if (app->options.in_filename)
    fclose (app->options.in);
}


int
qdpll_main (int argc, char **argv)
{
  QDPLLResult result = QDPLL_RESULT_UNKNOWN;
  QDPLLApp app;
  memset (&app, 0, sizeof (QDPLLApp));
  set_default_options (&app);

  qdpll = qdpll_create ();

  parse_cmd_line_options (&app, qdpll, argc, argv);
  check_options (&app);
  set_signal_handlers (&app);

  if (app.options.print_usage)
    {
      print_usage ();
      cleanup (qdpll, &app);
      return result;
    }
  if (app.options.print_version)
    {
      print_version ();
      cleanup (qdpll, &app);
      return result;
    }

  if (app.options.max_time)
    alarm (app.options.max_time);

  parse (&app, qdpll, app.options.in, app.options.trace);

  if (app.options.pretty_print)
    qdpll_print (qdpll, stdout);
  else if (app.options.deps_only)
    {
      qdpll_init_deps (qdpll);
      if (app.options.print_deps)
        print_deps (&app, qdpll);
      if (app.options.dump_dep_graph)
        qdpll_dump_dep_graph (qdpll);
    }
  else
    {
      result = qdpll_sat (qdpll);
#if (COMPUTE_STATS || COMPUTE_TIMES)
      qdpll_print_stats (qdpll);
#endif
    }

  if (app.options.trace == TRACE_QRP)
    fprintf (stdout, "r ");
  else if (app.options.trace == TRACE_BQRP)
    fprintf (stdout, "%cr ", 0);

  print_result_message (&app, qdpll, result);

  cleanup (qdpll, &app);

  return result;
}
