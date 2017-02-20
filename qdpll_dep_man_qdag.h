/*
 This file is part of DepQBF.

 DepQBF, a solver for quantified boolean formulae (QBF).        
 Copyright 2013, 2014, 2015, 2016, 2017 Florian Lonsing,
   Vienna University of Technology, Vienna, Austria.
 Copyright 2010, 2011, 2012 Florian Lonsing,
   Johannes Kepler University, Linz, Austria.
 Copyright 2012 Aina Niemetz,
   Johannes Kepler University, Linz, Austria.

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

#ifndef QDPLL_DEPMAN_QDAG_H_INCLUDED
#define QDPLL_DEPMAN_QDAG_H_INCLUDED

#include "qdpll_dep_man_generic.h"
#include "qdpll_pcnf.h"
#include "qdpll_mem.h"

typedef struct QDPLLDepManQDAG QDPLLDepManQDAG;

/* QDAG Dependency manager. */

/* Creates a qdag dependency manager. Last parameter indicates whether
to print dependencies by explicit search of CNF or by graph (for
testing only). */
QDPLLDepManQDAG *qdpll_qdag_dep_man_create (QDPLLMemMan * mm,
                                            QDPLLPCNF * pcnf,
                                            QDPLLDepManType type,
                                            int print_deps_by_search,
                                            QDPLL * qdpll);

/* Deletes a qdag dependency manager. */
void qdpll_qdag_dep_man_delete (QDPLLDepManQDAG * dm);

#endif
