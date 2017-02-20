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

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include <stddef.h>
#include "qdpll_mem.h"
#include "qdpll_exit.h"

#define QDPLL_ABORT_MEM(cond,msg)					\
  do {									\
    if (cond)								\
      {									\
        fprintf (stderr, "[qdpll_mem] %s at line %d: %s\n", __func__,	\
		 __LINE__,msg);						\
	fflush (stderr);						\
        abort ();							\
      }									\
  } while (0)

QDPLLMemMan *
qdpll_create_mem_man ()
{
  QDPLLMemMan *mm = (QDPLLMemMan *) malloc (sizeof (QDPLLMemMan));
  QDPLL_ABORT_MEM (!mm, "could not allocate memory!");
  memset (mm, 0, sizeof (QDPLLMemMan));
  return mm;
}


void
qdpll_delete_mem_man (QDPLLMemMan * mm)
{
  QDPLL_ABORT_MEM (!mm, "null pointer encountered!");
  assert (mm->cur_allocated == 0);
  free (mm);
}


void *
qdpll_malloc (QDPLLMemMan * mm, size_t size)
{
  /* Mem-limit is given in MB. */
  if (mm->limit && mm->limit < (mm->cur_allocated + size) / 1024 / 1024)
    {
      fprintf (stderr,
               "Attempted to allocate total %f MB (limit = %lu MB)\n",
               ((unsigned long) (mm->cur_allocated +
                                 size)) / 1024 / (float) 1024,
               (unsigned long) mm->limit);
      QDPLL_ABORT_MEM (1, "mem-limit exceeded!");
    }
  void *r = malloc (size);
  QDPLL_ABORT_MEM (!r, "could not allocate memory!");
  memset (r, 0, size);
  mm->cur_allocated += size;
  if (mm->cur_allocated > mm->max_allocated)
    mm->max_allocated = mm->cur_allocated;
  return r;
}


void *
qdpll_realloc (QDPLLMemMan * mm, void *ptr, size_t old_size, size_t new_size)
{
  ptr = realloc (ptr, new_size);
  QDPLL_ABORT_MEM (!ptr, "could not allocate memory!");
  if (new_size > old_size)
    memset (((char *) ptr) + old_size, 0, new_size - old_size);
  mm->cur_allocated -= old_size;
  mm->cur_allocated += new_size;
  if (mm->cur_allocated > mm->max_allocated)
    mm->max_allocated = mm->cur_allocated;
  return ptr;
}


void
qdpll_free (QDPLLMemMan * mm, void *ptr, size_t size)
{
  QDPLL_ABORT_MEM (!mm, "null pointer encountered!");
  free (ptr);
  mm->cur_allocated -= size;
}


size_t
qdpll_max_allocated (QDPLLMemMan * mm)
{
  return mm->max_allocated;
}


size_t
qdpll_cur_allocated (QDPLLMemMan * mm)
{
  return mm->cur_allocated;
}


void
qdpll_set_mem_limit (QDPLLMemMan * mm, size_t limit)
{
  QDPLL_ABORT_MEM (limit <= 0, "mem-limit must be greater than 0!");
  mm->limit = limit;
}


size_t
qdpll_get_mem_limit (QDPLLMemMan * mm)
{
  return mm->limit;
}
