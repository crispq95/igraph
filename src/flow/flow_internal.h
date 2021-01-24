/* -*- mode: C -*-  */
/*
   IGraph library.
   Copyright (C) 2021 The igraph development team

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc.,  51 Franklin Street, Fifth Floor, Boston, MA
   02110-1301 USA

*/

#ifndef IGRAPH_FLOW_INTERNAL_H
#define IGRAPH_FLOW_INTERNAL_H

#include "igraph_types.h"

__BEGIN_DECLS
igraph_error_t igraph_i_all_st_cuts_pivot(const igraph_t *graph,
                               const igraph_marked_queue_t *S,
                               const igraph_estack_t *T,
                               igraph_long_t source,
                               igraph_long_t target,
                               igraph_long_t *v,
                               igraph_vector_t *Isv,
                               void *arg);

__END_DECLS

#endif
