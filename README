
August 2013

-------------------
GENERAL INFORMATION
-------------------

This is version 2.0 of the search-based QBF solver DepQBF. Compared to the
previously released version 1.0, it includes the following major changes:

- Some code maintenance and bug fixes.

  Many thanks to Adam Foltzer and Allen Van Gelder for valuable feedback.

- Advanced clause and cube learning based on QBF Pseudo Unit Propagation as
  presented in the following paper: "Florian Lonsing, Uwe Egly, Allen Van
  Gelder: Efficient Clause Learning for Quantified Boolean Formulas via QBF
  Pseudo Unit Propagation. In Proc. SAT 2013."

  NOTE: by default, this version of DepQBF applies a lazy variant of
  QPUP-based QCDCL where no resolution steps are carried out. The traditional
  approach to QCDCL which was implemented in version 1.0 of DepQBF is still
  available by command line option '--traditional-qcdcl'. Please see also the
  command line documentation by calling './depqbf -h'.

Version 2.0 is the source-release of the version of DepQBF which participated
in the QBF Gallery 2013:

  http://www.kr.tuwien.ac.at/events/qbfgallery2013/


General features of DepQBF are:

- Generation of QDIMACS output (partial certificate): if the outermost
  (i.e. leftmost) quantifier block of a satisfiable QBF is existentially
  quantified, then DepQBF can print an assignment to the variables of this
  block (and dually for unsatisfiable QBFs and universal variables from the
  outermost block, if that block is universally quantified). To enable QDIMACS
  output generation, run DepQBF with parameter '--qdo'. Note that the
  assignment printed by DepQBF can be partial, i.e. not all variables are
  necessarily assigned.

- Trace generation (contributed by Aina Niemetz): DepQBF can produce
  traces in QRP format (ASCII and binary version of the QRP format are
  supported; see also usage information). If called with the '--trace' option,
  the solver prints *every* resolution step during clause and cube learning to
  <stdout>. The output format is QRP ("Q-Resolution Proof"). For example, the
  call './depqbf --trace input-formula.qdimacs > trace.qrp' dumps the trace
  for the QBF 'input-formula.qdimacs' to the file 'trace.qrp'. The generated
  trace file can be used to extract a certificate of (un)satisfiability of the
  given formula using additional tools. See also the website 
  'http://fmv.jku.at/cdepqbf/' and the related tool paper published at SAT'12.

  NOTE: tracing must be combined with the trivial dependency scheme (i.e. the
  linear quantifier prefix ordering) by option '--dep-man=simple'. Further, to
  enable tracing for QPUP-based QCDCL, '--no-lazy-qpup' must be specified.

- The solver can be used as a library. The API is declared in file 'qdpll.h'
  and file 'qdpll_app.c' demonstrates how it can be used. Note that the API,
  apart from basic use, has not yet been thoroughly tested.

DepQBF is free software released under GPLv3. See also file COPYING. Please do
not hesitate to contact Florian Lonsing (see below) for any questions related
to DepQBF.

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


------------
INSTALLATION
------------

Unpack the sources into a directory and call 'make'. This produces optimized
code without assertions (default).

Note: set the flag 'FULL_ASSERT' in file 'qdpll_config.h' from 0 to 1 to
switch on *expensive* assertions (recommended only for debugging). The solver
will run *substantially* slower in this case. As usual, the compiler flag
'DNDEBUG' removes all assertions from the code, regardless from the value of
'FULL_ASSERT'.


-----------------------
CONFIGURATION AND USAGE
-----------------------

Call './depqbf -h' to display usage information. Further, undocumented command
line parameters can be found in function 'qdpll_configure(...)' in file
'qdpll.c'.

The solver returns exit code 10 if the given instance was found satisfiable and exit
code 20 if the instance was found unsatisfiable. Any other exit code indicates
that the instance was not solved.

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


----------
REFERENCES
----------

@article{DBLP:journals/jsat/LonsingB10,
  author    = {Florian Lonsing and
               Armin Biere},
  title     = {DepQBF: A Dependency-Aware QBF Solver},
  journal   = {JSAT},
  volume    = {7},
  number    = {2-3},
  year      = {2010},
  pages     = {71-76},
  ee        = {http://jsat.ewi.tudelft.nl/content/volume7/JSAT7_6_Lonsing.pdf},
  bibsource = {DBLP, http://dblp.uni-trier.de}
}

@inproceedings{DBLP:conf/sat/NiemetzPLSB12,
  author    = {Aina Niemetz and
               Mathias Preiner and
               Florian Lonsing and
               Martina Seidl and
               Armin Biere},
  title     = {Resolution-Based Certificate Extraction for QBF - (Tool
               Presentation)},
  booktitle = {SAT},
  year      = {2012},
  pages     = {430-435},
  ee        = {http://dx.doi.org/10.1007/978-3-642-31612-8_33},
  crossref  = {DBLP:conf/sat/2012},
  bibsource = {DBLP, http://dblp.uni-trier.de}
}

@inproceedings{DBLP:conf/sat/LonsingEG13,
  author    = {Florian Lonsing and
               Uwe Egly and
               Allen Van Gelder},
  title     = {Efficient Clause Learning for Quantified Boolean Formulas
               via QBF Pseudo Unit Propagation},
  booktitle = {SAT 2013},
  year      = {2013},
  pages     = {100-115},
  ee        = {http://dx.doi.org/10.1007/978-3-642-39071-5_9},
  crossref  = {DBLP:conf/sat/2013},
  bibsource = {DBLP, http://dblp.uni-trier.de}
}

-------
CONTACT
-------

For comments, questions, bug reports etc. related to DepQBF please contact Florian Lonsing.

See also http://www.kr.tuwien.ac.at/staff/lonsing/ and http://lonsing.github.io/depqbf/
