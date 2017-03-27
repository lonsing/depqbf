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

#ifndef QDPLL_STACK_H_INCLUDED
#define QDPLL_STACK_H_INCLUDED

#include "qdpll_mem.h"

#define QDPLL_DECLARE_STACK(name, type)					\
  typedef struct name ## Stack name ## Stack;				\
  struct name ## Stack { type * start; type * top; type * end; }

#define QDPLL_INIT_STACK(stack)			   \
  do {						   \
    (stack).start = (stack).top = (stack).end = 0; \
  } while (0)

#define QDPLL_ADJUST_STACK(mm,stack,size)				\
  do {									\
    size_t old_size;							\
    if ((size) > 0 && (old_size = QDPLL_SIZE_STACK(stack)) < (size))	\
      {									\
	size_t elem_bytes = sizeof(*(stack).start);			\
	size_t old_count = QDPLL_COUNT_STACK (stack);			\
	(stack).start = qdpll_realloc((mm), (stack).start,		\
				      old_size * elem_bytes,		\
				      (size) * elem_bytes);		\
	(stack).top = (stack).start + old_count;			\
	(stack).end = (stack).start + (size);				\
      }									\
  }while(0)								\

#define QDPLL_COUNT_STACK(stack) ((size_t) ((stack).top - (stack).start))
#define QDPLL_EMPTY_STACK(stack) ((stack).top == (stack).start)
#define QDPLL_RESET_STACK(stack) do { (stack).top = (stack).start; } while (0)

#define QDPLL_SIZE_STACK(stack) ((stack).end - (stack).start)
#define QDPLL_FULL_STACK(stack) ((stack).top == (stack).end)

#define QDPLL_DELETE_STACK(mm, stack)					\
  do {									\
    qdpll_free((mm), (stack).start,					\
	       QDPLL_SIZE_STACK(stack) * sizeof(*(stack).start));	\
    QDPLL_INIT_STACK ((stack));						\
  } while (0)

#define QDPLL_ENLARGE_STACK(mm, stack)					\
  do {									\
    size_t old_size = QDPLL_SIZE_STACK (stack), new_size;		\
    new_size = old_size ? 2 * old_size : 1;				\
    size_t old_count = QDPLL_COUNT_STACK (stack);			\
    size_t elem_bytes = sizeof(*(stack).start);				\
    (stack).start = qdpll_realloc((mm), (stack).start,			\
				  old_size*elem_bytes,			\
				  new_size*elem_bytes);			\
    (stack).top = (stack).start + old_count;				\
    (stack).end = (stack).start + new_size;				\
  } while (0)

#define QDPLL_PUSH_STACK(mm, stack, elem)	\
  do {						\
    if (QDPLL_FULL_STACK ((stack)))		\
      QDPLL_ENLARGE_STACK ((mm), (stack));	\
    *((stack).top++) = (elem);			\
  } while (0)

#define QDPLL_POP_STACK(stack) (*--(stack).top)

QDPLL_DECLARE_STACK (VoidPtr, void *);
QDPLL_DECLARE_STACK (CharPtr, char *);

#endif
