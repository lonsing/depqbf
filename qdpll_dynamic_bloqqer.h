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

#ifndef QDPLL_DYNAMIC_BLOQQER_H_INCLUDED
#define QDPLL_DYNAMIC_BLOQQER_H_INCLUDED

#include "qdpll.h"
#include "./bloqqer35/bloqqer.h"

enum BloqqerResult
{
  BLOQQER_RESULT_UNKNOWN = 0,
  BLOQQER_RESULT_SAT = 10,
  BLOQQER_RESULT_UNSAT = 20
};

typedef enum BloqqerResult BloqqerResult;

BloqqerResult dynamic_bloqqer_test (QDPLL *qdpll);

#endif
