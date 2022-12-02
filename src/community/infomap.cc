/* -*- mode: C -*-  */
/*
   IGraph library.
   Copyright (C) 2011-2012  Gabor Csardi <csardi.gabor@gmail.com>
   334 Harvard street, Cambridge, MA 02139 USA

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
   Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
   02110-1301 USA

   ----
   The original version of this file was written by Martin Rosvall
   email: martin.rosvall@physics.umu.se
   homePage: http://www.tp.umu.se/~rosvall/

   It was integrated in igraph by Emmanuel Navarro
   email: navarro@irit.fr
   homePage: http://www.irit.fr/~Emmanuel.Navarro/
*/

#include "igraph_community.h"

#include "igraph_interface.h"

#include "core/exceptions.h"
#include "core/interruption.h"

#include "infomap/src/Infomap.h"

#include <vector>
#include <cmath>

/**
 * \function igraph_community_infomap
 * \brief Find community structure that minimizes the expected description length of a random walker trajectory.
 *
 * Implementation of the InfoMap community detection algorithm of
 * Martin Rosvall and Carl T. Bergstrom.
 *
 * </para><para>
 * For more details, see the visualization of the math and the map generator
 * at https://www.mapequation.org . The original paper describing the algorithm
 * is: M. Rosvall and C. T. Bergstrom, Maps of information flow reveal community
 * structure in complex networks, PNAS 105, 1118 (2008)
 * (http://dx.doi.org/10.1073/pnas.0706851105, http://arxiv.org/abs/0707.0609).
 * A more detailed paper about the algorithm is: M. Rosvall, D. Axelsson, and
 * C. T. Bergstrom, The map equation, Eur. Phys. J. Special Topics 178, 13 (2009).
 * (http://dx.doi.org/10.1140/epjst/e2010-01179-1, http://arxiv.org/abs/0906.1405)

 * </para><para>
 * The original C++ implementation of Martin Rosvall is used,
 * see http://www.tp.umu.se/~rosvall/downloads/infomap_undir.tgz .
 * Integration in igraph was done by Emmanuel Navarro (who is grateful to
 * Martin Rosvall and Carl T. Bergstrom for providing this source code).
 *
 * </para><para>
 * Note that the graph must not contain isolated vertices.
 *
 * </para><para>
 * If you want to specify a random seed (as in the original
 * implementation) you can use \ref igraph_rng_seed().
 *
 * \param graph The input graph.
 * \param e_weights Numeric vector giving the weights of the edges.
 *     The random walker will favour edges with high weights over
 *     edges with low weights; the probability of picking a particular
 *     outbound edge from a node is directly proportional to its weight.
 *     If it is a NULL pointer then all edges will have equal
 *     weights. The weights are expected to be positive.
 * \param v_weights Numeric vector giving the weights of the vertices.
 *     Vertices with higher weights are favoured by the random walker
 *     when it needs to "teleport" to a new node after getting stuck in
 *     a sink node (i.e. a node with no outbound edges). The probability
 *     of picking a vertex when the random walker teleports is directly
 *     proportional to the weight of the vertex. If this argument is a NULL
 *     pointer then all vertices will have equal weights. Weights are expected
 *     to be positive.
 * \param nb_trials The number of attempts to partition the network
 *     (can be any integer value equal or larger than 1).
 * \param membership Pointer to a vector. The membership vector is
 *    stored here.
 * \param codelength Pointer to a real. If not NULL the code length of the
 *     partition is stored here.
 * \return Error code.
 *
 * \sa \ref igraph_community_spinglass(), \ref
 * igraph_community_edge_betweenness(), \ref igraph_community_walktrap().
 *
 * Time complexity: TODO.
 */
igraph_error_t igraph_community_infomap(const igraph_t * graph,
                             const igraph_vector_t *e_weights,
                             const igraph_vector_t *v_weights,
                             igraph_integer_t nb_trials,
                             igraph_vector_int_t *membership,
                             igraph_real_t *codelength) {

    IGRAPH_HANDLE_EXCEPTIONS(

        // Create infomap wrapper
        infomap::InfomapWrapper iw("--two-level -N2");;
        
        igraph_integer_t n = igraph_vcount(graph);
        igraph_integer_t m = igraph_ecount(graph);

        for (igraph_integer_t v = 0; v < n; v++)
        {
            iw.addNode(v, VECTOR(*v_weights)[v]);
        }

        for (igraph_integer_t e = 0; e < m; e++)
        {
            igraph_integer_t v1 = IGRAPH_FROM(graph, e);
            igraph_integer_t v2 = IGRAPH_TO(graph, e);
            iw.addLink(v1, v2, VECTOR(*e_weights)[e]);
        }
        
        // Run main infomap algorithm
        iw.run();

        // Retrieve membership
        for (auto it = iw.iterTree(); !it.isEnd(); ++it) 
        {
            VECTOR(*membership)[it->physicalId] = it.moduleIndex();
        }

        // Re-index membership
        IGRAPH_CHECK(igraph_reindex_membership(membership, 0, 0));

        return IGRAPH_SUCCESS;
    );
}

