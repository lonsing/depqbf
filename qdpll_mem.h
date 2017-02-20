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

#ifndef QDPLL_MEM_H_INCLUDED
#define QDPLL_MEM_H_INCLUDED

#include <stddef.h>

struct QDPLLMemMan
{
  size_t cur_allocated;
  size_t max_allocated;
  size_t limit;
};

typedef struct QDPLLMemMan QDPLLMemMan;

QDPLLMemMan *qdpll_create_mem_man ();

void qdpll_delete_mem_man (QDPLLMemMan * mm);

void *qdpll_malloc (QDPLLMemMan * mm, size_t size);

void *qdpll_realloc (QDPLLMemMan * mm, void *ptr, size_t old_size,
                     size_t new_size);

void qdpll_free (QDPLLMemMan * mm, void *ptr, size_t size);

size_t qdpll_max_allocated (QDPLLMemMan * mm);

size_t qdpll_cur_allocated (QDPLLMemMan * mm);

void qdpll_set_mem_limit (QDPLLMemMan * mm, size_t limit);

size_t qdpll_get_mem_limit (QDPLLMemMan * mm);

#endif
