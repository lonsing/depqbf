
February 2015

-------------------
GENERAL INFORMATION
-------------------

This is version 4.0 of the search-based QBF solver DepQBF.  Compared to the
previously released versions, DepQBF 4.0 includes a novel API to support
incremental solving based on clause groups. A clause group is a set of clauses
which is incrementally added to and removed from a formula. A description of
the API can be found in the following technical report:

Florian Lonsing and Uwe Egly: 
"DepQBF: An Incremental QBF Solver Based on Clause Groups". 
Technical report, arXiv/CoRR, February 2015. http://arxiv.org/abs/1502.02484

This release of DepQBF comes with DepQBF4J, a Java interface to DepQBF which
allows to call DepQBF as a library from Java programs. Please see the README
file in the subdirectory './DepQBF4J-0.2' for further information and usage
examples. DepQBF4J is based on the Java Native Interface (JNI) and was
implemented by Martin Kronegger and Andreas Pfandler.

PLEASE SEE the header file 'qdpll.h', the examples in the subdirectory
'examples', and the command line documentation (call './depqbf -h') for
further information on using DepQBF and its library.

PLEASE SEE ALSO the guidelines on incremental solving and API usage below.

The example './examples/basic-api-example2.c' demonstrates the basic use of
the API and, in particular, the 'qdpll_gc' function. The clause group API is
illustrated by './examples/basic-clause-groups-api-example.c'

Many thanks to Robert Koenighofer, Adria Gascon, Thomas Krennwallner, Martin
Kronegger, Andreas Pfandler, and Simon Cruanes for valuable feedback.

--------
FEATURES
--------

General features of DepQBF:

- The solver can be used as a library. The API is declared in file 'qdpll.h'
  and the examples in the subdirectory 'examples' demonstrate its basic use.

- Incremental solving: Incremental solving can be beneficial in applications
  where a sequence of closely related formulae must be solved. This way, the
  solver does not have to solve each formula from scratch but tries to reuse
  information learned from previously solved formulae. DepQBF supports
  incremental solving by a push/pop API and a clause group API. The push/pop
  API allows to add and remove sets of clauses in a stack-based way. The
  clause group API is more general and supports addition and deletion of
  arbitrary sets of clauses.

- Extraction of unsatisfiable cores: for unsatisfiable formulas, an
  unsatisfiable core (i.e. subset of clauses) can be extracted via the clause
  group API in a convenient way.

- Solving under assumptions: assumptions are fixed variable assignments from
  the leftmost quantifier block of a QBF. Assumptions can be added through the
  solver API. In forthcoming calls, the solver tries to solve the formula
  under the assignments given by the added assumptions.

- Long-distance resolution for clause and cube learning: traditional
  Q-resolution explicitly rules out the generation of tautological
  resolvents. In contrast to that, long-distance resolution admits certain
  tautological resolvents. It was first implemented in the QBF solver
  'quaffle' and is now also available in DepQBF.

- Advanced clause and cube learning based on QBF Pseudo Unit Propagation as
  presented in the following paper: "Florian Lonsing, Uwe Egly, Allen Van
  Gelder: Efficient Clause Learning for Quantified Boolean Formulas via QBF
  Pseudo Unit Propagation. In Proc. SAT 2013."

  NOTE: by default, this version of DepQBF applies a lazy variant of
  QPUP-based QCDCL where no resolution steps are carried out. The traditional
  approach to QCDCL which was implemented in earlier versions of DepQBF is
  still available by command line option '--traditional-qcdcl'. Please see
  also the command line documentation by calling './depqbf -h'.

- Generation of QDIMACS output (partial certificate): if the outermost
  (i.e. leftmost) quantifier block of a satisfiable QBF is existentially
  quantified, then DepQBF can print an assignment to the variables of this
  block (and dually for unsatisfiable QBFs and universal variables from the
  outermost block, if that block is universally quantified). To enable QDIMACS
  output generation, run DepQBF with parameter '--qdo'. Note that the
  assignment printed by DepQBF can be partial, i.e. not all variables are
  necessarily assigned. In this case, the variables for which no value was
  printed can be assigned arbitrarily.

- Trace generation (contributed by Aina Niemetz): DepQBF can produce traces in
  QRP format (ASCII and binary version of the QRP format are supported; see
  also the command line documentation). If called with the '--trace' option,
  the solver prints *every* resolution step during clause and cube learning to
  <stdout>. The output format is QRP ("Q-Resolution Proof"). For example, the
  call './depqbf --trace input-formula.qdimacs > trace.qrp' dumps the trace
  for the QBF 'input-formula.qdimacs' to the file 'trace.qrp'. The generated
  trace file can be used to extract a certificate of (un)satisfiability of the
  given formula using additional tools. See also the website
  'http://fmv.jku.at/qbfcert/' and the related tool paper published at SAT'12.

  NOTE: tracing is currently not supported in incremental solving and must be
  combined with the trivial dependency scheme (i.e. the linear quantifier
  prefix ordering) by option '--dep-man=simple'. Further, to enable tracing
  for QPUP-based QCDCL, '--no-lazy-qpup' must be specified.

DepQBF consists of a dependency manager (file 'qdpll_dep_man_qdag.c') and a
core QDPLL solver (file 'qdpll.c'). During a run the solver queries the
dependency manager to find out if there is a dependency between two variables,
say 'x' and 'y'. Given the original quantifier prefix of a QBF, there is such
dependency if 'x' is quantified to the left of 'y' and 'x' and 'y' are
quantified differently. In contrast to that simple approach, DepQBF (in
general) is able to extract more sophisticated dependency information from the
given QBF. It computes the so-called 'standard dependency scheme' which is
represented as a compact graph by the dependency manager.

If you are interested only in the core solver based on QDPLL then it is
probably best not to look at the code of the dependency manager in file
'qdpll_dep_man_qdag.c' at all but only consider file 'qdpll.c'.


-------
LICENSE
-------

DepQBF is free software released under GPLv3:

https://www.gnu.org/copyleft/gpl.html

See also the file COPYING.


------------
INSTALLATION
------------

The latest release is available from http://lonsing.github.io/depqbf/

Unpack the sources into a directory and call 'make'. This produces optimized
code without assertions (default).

If you want to use the solver as a library in your own applications, then link
against 'libqdpll.a'.

Note: set the flag 'FULL_ASSERT' in file 'qdpll_config.h' from 0 to 1 to
switch on *expensive* assertions (recommended only for debugging). The solver
will run *substantially* slower in this case. As usual, using the compiler
flag 'DNDEBUG' removes all assertions from the code, regardless from the value
of 'FULL_ASSERT'.

Compilation on a Mac:

Depending on your system, it might be necessary to replace "-soname"
by "-install_name" in the makefile.


-----------------------
CONFIGURATION AND USAGE
-----------------------

Call './depqbf -h' to display usage information. Further, undocumented command
line parameters can be found in function 'qdpll_configure(...)' in file
'qdpll.c'. These parameters are mostly experimental.

The solver returns exit code 10 if the given instance was found satisfiable
and exit code 20 if the instance was found unsatisfiable. Any other exit code
indicates that the instance was not solved.

Parameter '-v' enables basic verbose mode where the solver prints information
on restarts and backtracks to <stderr>. More occurrences of '-v' result in
heavy verbose mode where information on individual assignments is
printed. This can slow down the solver considerably and should be used for
debugging only.

Trace generation can be enabled by parameter '--trace'. Note that printing the
tracing information causes I/O overhead and might slow down the
solver. Writing traces in binary QRP format (enabled by parameter
'--trace=bqrp') usually produces smaller traces, as far as byte size is
concerned.

Calling DepQBF without command line parameters results in default behaviour
which was tuned on instances from QBFLIB. For performance comparisons with
other solvers it is recommended not to pass any command line parameters to
DepQBF.

By default, statistical output is disabled. To enable statistics, set the flag
'COMPUTE_STATS' in file 'qdpll_config.h' from 0 to 1. Similarly, time
statistics can be enabled by setting flag 'COMPUTE_STATS'.


-------------------------------
IMPORTANT NOTE ON PREPROCESSING
-------------------------------

DepQBF is a plain solver and does not have built-in preprocessing. However,
preprocessing typically increases the performance considerably. It is highly
recommended -- for non-incremental solving -- to combine DepQBF with
preprocessors such as Bloqqer and/or QxBF, for example:

http://fmv.jku.at/bloqqer/

http://fmv.jku.at/qxbf/


----------------------------------------------------
IMPORTANT NOTES ON INCREMENTAL SOLVING AND API USAGE
----------------------------------------------------

Please see the header file 'qdpll.h' for some documentation of the API
functions.

When using the API of the solver (versions 3.0 up to 4.0), it is HIGHLY
RECOMMENDED to first add all the variables to the quantifier prefix and then
all the clauses of the formula rather than adding variables and clauses in
interleaved fashion. In the latter case, runtime overhead will occur for large
formulas. Many thanks to Mathias Preiner for pointing out this problem.

In applications which involve a very large number of incremental calls, the
overhead of maintaining the internal data structures in this release of DepQBF
might become non-negligible. In this case, please contact Florian Lonsing;
your feedback is highly appreciated.

Incremental solving must be enabled by calling the API function
'qdpll_configure' with the parameters '--dep-man=simple' and
'--incremental-use', respectively. Please see also the example programs in the
subdirectory 'examples'.

The push/pop API allows to add and remove clauses in a stack-based
way. Therefore, clauses which are shared between many formulas to be solved
should be pushed onto the stack first. Clauses which have to be removed soon
should be added last so that they can be popped from the stack easily.

In general, it is beneficial for the performance of the solver to avoid
needless push operations. For example, if you know that certain clauses will
never be removed from the formula then it is not necessary to call
'qdpll_push' before adding these clauses.

The clause group API generalizes the push/pop API in that it allows sets of
clauses to be added and removed arbitrarily. It is recommended to use the
push/pop API instead of the clause group API for applications which naturally
can be encoded by push and pop operations, that is, where the formulas to be
solved incrementally are modified in a rather uniform way.

If assumptions are passed to the solver using 'qdpll_assume' AND clauses are
added later to the formula, then the API function 'qdpll_configure' must be
called with the parameters '--dep-man=simple' and '--incremental-use' after
the solver object has been created by 'qdpll_create'. Otherwise, if no clauses
are added, then the aforementioned calls of the API function 'qdpll_configure'
can be omitted.


-------
CONTACT
-------

For comments, questions, bug reports etc. related to DepQBF, please do not
hesitate to contact Florian Lonsing:

http://www.kr.tuwien.ac.at/staff/lonsing/ 

http://lonsing.github.io/depqbf/
