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

#ifndef QDPLL_DEPMAN_GENERIC_H_INCLUDED
#define QDPLL_DEPMAN_GENERIC_H_INCLUDED

#include "qdpll_pcnf.h"
#include "qdpll_mem.h"
#include "qdpll.h"

enum QDPLLDepManType
{
  QDPLL_DEPMAN_TYPE_QDAG = 0,
  QDPLL_DEPMAN_TYPE_SIMPLE = 1
};

typedef enum QDPLLDepManType QDPLLDepManType;

typedef struct QDPLLDepManGeneric QDPLLDepManGeneric;

struct QDPLLDepManGeneric
{
  QDPLL *qdpll;
  QDPLLDepManType type;
  void (*init) (QDPLLDepManGeneric * dm);
  void (*reset) (QDPLLDepManGeneric * dm);
    VarID (*get_candidate) (QDPLLDepManGeneric * dm);
  void (*notify_inactive) (QDPLLDepManGeneric * dm, VarID id);
  void (*notify_active) (QDPLLDepManGeneric * dm, VarID id);
  int (*is_candidate) (QDPLLDepManGeneric * dm, VarID id);
  void (*notify_init_variable) (QDPLLDepManGeneric * dm, VarID id);
  void (*notify_reset_variable) (QDPLLDepManGeneric * dm, VarID id);
  int (*is_init) (QDPLLDepManGeneric * dm);
  void (*print_deps) (QDPLLDepManGeneric * dm, VarID id);
  void (*dump_dep_graph) (QDPLLDepManGeneric * dm);
  int (*depends) (QDPLLDepManGeneric * dm, VarID x, VarID y);
  void (*reduce_lits) (QDPLLDepManGeneric * dm,
                       LitIDStack ** lit_stack, LitIDStack ** lit_stack_tmp,
                       const QDPLLQuantifierType other_type,
                       const int lits_sorted);

  /* Used in 'choose-var' and 'type-red'. */
    VarID (*get_class_rep) (QDPLLDepManGeneric * dmg, VarID x,
                            const unsigned int ufoffset);

  LitID * (*get_candidates) (QDPLLDepManGeneric * dm);
};

#endif
