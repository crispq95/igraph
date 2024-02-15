/* -*- mode: C -*-  */
/* vim:set ts=4 sw=4 sts=4 et: */
/*
   IGraph library.
   Copyright (C) 2007-2020  The igraph development team <igraph@igraph.org>

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.
*/

#include <igraph.h>
#include <stdio.h>
#include <stdlib.h>


int main() {
   igraph_t graph;
   igraph_vector_t membership, initial;
   igraph_real_t modularity;

   FILE *graph_file;

   // hay que arreglar ficheros de : email-Eu-core.txt, amazon, email-enron, dblp -> no self loops, no 2 times 1 edge ?
   // test graph from graph compression paper  graph_compressed_test.txt
   //   graph_compressed_test.txt
   // /home/crispq/label_propagation/graphs/with_gt/com-dblp.ungraph.txt  // com-amazon.ungraph.txt -> 300k nodos
   // /home/crispq/label_propagation/soc-dolphins.mtx
   graph_file = fopen("/home/crispq/label_propagation/web-uk.txt", "rb"); 
    if (!graph_file) {
        return 1;
    }

   // igraph_famous(&graph, "Zachary"); /* We use Zachary's karate club network. */

   // /* HOW TO LOAD A GRAPH ? */
   // // file is an edge list 
   igraph_read_graph_edgelist(&graph, graph_file, 0, IGRAPH_UNDIRECTED);

   /* Label propagation is a stochastic method; the result will depend on the random seed. */
   // igraph_rng_seed(igraph_rng_default(), 123);

   /* All igraph functions that returns their result in an igraph_vector_t must be given
      an already initialized vector. */
   igraph_vector_init(&membership, igraph_vcount(&graph));

   // create initial vector and fill with -1 -> meaning no labels at the beggining 
   igraph_vector_init(&initial, igraph_vcount(&graph)); 
   igraph_vector_fill(&initial, -1);

   // igraph_community_label_propagation(
   //              &graph, &membership,
   //              /* weights= */ NULL, /* initial= */&initial, /* fixed= */ NULL,
   //              &modularity, IGRAPH_CK_LPA);

   // igraph_community_label_propagation(
   //              &graph, &membership,
   //              /* weights= */ NULL, /* initial= */&initial, /* fixed= */ NULL,
   //              &modularity, IGRAPH_DPC_LPA);

   igraph_community_label_propagation(
                &graph, &membership,
                /* weights= */ NULL, /* initial= */NULL, /* fixed= */ NULL,
                &modularity, IGRAPH_LPA_FAST); //DOMINANCE

   // 
   igraph_modularity(
        &graph, &membership, /* weights= */ NULL, /* resolution = */ 1,
        /* directed= */ 0, &modularity);

   printf("%ld communities found; modularity score is %g.\n",
         (long int) (igraph_vector_max(&membership) + 1),
         modularity);

   // sizes of the found communties
   // igraph_vector_t comm_size;
   // igraph_vector_init(&initial, igraph_vcount(&graph)); 


   // printf("Communities membership: ");
   // igraph_vector_print(&membership);

   fclose(graph_file);

   /* Destroy data structures at the end. */
   igraph_vector_destroy(&membership);
   igraph_destroy(&graph);

   return 0;
}
