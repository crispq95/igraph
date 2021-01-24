/* -*- mode: C -*-  */
/*
   IGraph library.
   Copyright (C) 2009-2020  The igraph development team

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

#ifndef IGRAPH_CORE_GRID_H
#define IGRAPH_CORE_GRID_H

#undef __BEGIN_DECLS
#undef __END_DECLS
#ifdef __cplusplus
    #define __BEGIN_DECLS extern "C" {
    #define __END_DECLS }
#else
    #define __BEGIN_DECLS /* empty */
    #define __END_DECLS /* empty */
#endif

#include "igraph_types.h"
#include "igraph_matrix.h"
#include "igraph_vector.h"

__BEGIN_DECLS

/**
 * 2d grid containing points
 */

typedef struct igraph_2dgrid_t {
    igraph_matrix_t *coords;
    igraph_real_t minx, maxx, deltax;
    igraph_real_t miny, maxy, deltay;
    igraph_long_t stepsx, stepsy;
    igraph_matrix_t startidx;
    igraph_vector_t next;
    igraph_vector_t prev;
    igraph_real_t massx, massy;       /* The sum of the coordinates */
    igraph_long_t vertices;        /* Number of active vertices  */
} igraph_2dgrid_t;
igraph_error_t igraph_2dgrid_init(igraph_2dgrid_t *grid, igraph_matrix_t *coords,
                       igraph_real_t minx, igraph_real_t maxx, igraph_real_t deltax,
                       igraph_real_t miny, igraph_real_t maxy, igraph_real_t deltay);
void igraph_2dgrid_destroy(igraph_2dgrid_t *grid);
void igraph_2dgrid_add(igraph_2dgrid_t *grid, igraph_long_t elem,
                       igraph_real_t xc, igraph_real_t yc);
void igraph_2dgrid_add2(igraph_2dgrid_t *grid, igraph_long_t elem);
void igraph_2dgrid_move(igraph_2dgrid_t *grid, igraph_long_t elem,
                        igraph_real_t xc, igraph_real_t yc);
void igraph_2dgrid_getcenter(const igraph_2dgrid_t *grid,
                             igraph_real_t *massx, igraph_real_t *massy);
igraph_bool_t igraph_2dgrid_in(const igraph_2dgrid_t *grid, igraph_long_t elem);
igraph_real_t igraph_2dgrid_dist(const igraph_2dgrid_t *grid,
                                 igraph_long_t e1, igraph_long_t e2);
igraph_error_t igraph_2dgrid_neighbors(igraph_2dgrid_t *grid, igraph_vector_t *eids,
                            igraph_long_t vid, igraph_real_t r);

typedef struct igraph_2dgrid_iterator_t {
    igraph_long_t vid, x, y;
    igraph_long_t nei;
    igraph_long_t nx[4], ny[4], ncells;
} igraph_2dgrid_iterator_t;

void igraph_2dgrid_reset(igraph_2dgrid_t *grid, igraph_2dgrid_iterator_t *it);
igraph_error_t igraph_2dgrid_next(igraph_2dgrid_t *grid,
                                    igraph_2dgrid_iterator_t *it);
igraph_error_t igraph_2dgrid_next_nei(igraph_2dgrid_t *grid,
                                        igraph_2dgrid_iterator_t *it);

__END_DECLS

#endif
