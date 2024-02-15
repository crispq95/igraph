/* -*- mode: C -*-  */
/* vim:set ts=4 sw=4 sts=4 et: */
/*
   IGraph library.
   Copyright (C) 2007-2020 The igraph development team

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

*/

#include "igraph_community.h"

#include "igraph_adjlist.h"
#include "igraph_dqueue.h"
#include "igraph_interface.h"
#include "igraph_memory.h"
#include "igraph_random.h"

int igraph_i_community_label_propagation(const igraph_t *graph,
    igraph_vector_t *membership,
    const igraph_vector_t *weights,
    igraph_vector_bool_t *fixed,
    igraph_bool_t retention)
{
  long int no_of_nodes = igraph_vcount(graph);
  long int no_of_not_fixed_nodes = 0;
  long int i, j, k;
  igraph_adjlist_t al;
  igraph_inclist_t il;
  igraph_bool_t running, control_iteration;
  igraph_vector_t label_counters, dominant_labels, nonzero_labels, node_order;

  /* Create an adjacency/incidence list representation for efficiency.
   * For the unweighted case, the adjacency list is enough. For the
   * weighted case, we need the incidence list */
  if (weights) {
    IGRAPH_CHECK(igraph_inclist_init(graph, &il, IGRAPH_IN, IGRAPH_LOOPS_ONCE));
    IGRAPH_FINALLY(igraph_inclist_destroy, &il);
  } else {
    IGRAPH_CHECK(igraph_adjlist_init(graph, &al, IGRAPH_IN, IGRAPH_LOOPS_ONCE, IGRAPH_MULTIPLE));
    IGRAPH_FINALLY(igraph_adjlist_destroy, &al);
  }

  /* Create storage space for counting distinct labels and dominant ones */
  IGRAPH_VECTOR_INIT_FINALLY(&label_counters, no_of_nodes);
  IGRAPH_VECTOR_INIT_FINALLY(&dominant_labels, 0);
  IGRAPH_VECTOR_INIT_FINALLY(&nonzero_labels, 0);
  IGRAPH_CHECK(igraph_vector_reserve(&dominant_labels, 2));

  /* Initialize node ordering vector with only the not fixed nodes */
  if (fixed) {
    IGRAPH_VECTOR_INIT_FINALLY(&node_order, no_of_nodes);
    for (i = 0; i < no_of_nodes; i++) {
      if (!VECTOR(*fixed)[i]) {
        VECTOR(node_order)[no_of_not_fixed_nodes] = i;
        no_of_not_fixed_nodes++;
      }
    }
    IGRAPH_CHECK(igraph_vector_resize(&node_order, no_of_not_fixed_nodes));
  } else {
    IGRAPH_CHECK(igraph_vector_init_seq(&node_order, 0, no_of_nodes - 1));
    IGRAPH_FINALLY(igraph_vector_destroy, &node_order);
    no_of_not_fixed_nodes = no_of_nodes;
  }

  RNG_BEGIN();

  /* There are two modes of operation in this implementation: retention or
   * dominance. When using retention, we prefer to keep the current label of a node.
   * Only if the current label is not among the dominant labels will we
   * update the label. If a label changes, we will continue to iterate
   * over all nodes.
   *
   * When not using retention we check for dominance after each iteration. This
   * is implemented as two alternating types of iterations, one for changing
   * labels and the other one for checking the end condition - every vertex in the
   * graph has a label to which the maximum number of its neighbors belongs. If
   * control_iteration is true, we are just checking the end condition and not
   * relabeling nodes.
   */
  control_iteration = 1;
  running = 1;
  while (running) {
    long int v1, num_neis;
    igraph_real_t max_count;
    igraph_vector_int_t *neis;
    igraph_vector_int_t *ineis;
    igraph_bool_t was_zero;

    if (retention) {
        /* We stop in this iteration by default, unless a label changes */
        running = 0;
        /* Shuffle the node ordering vector */
        IGRAPH_CHECK(igraph_vector_shuffle(&node_order));
    }
    else {
        if (control_iteration) {
            /* If we are in the control iteration, we expect in the begining of
            the iterationthat all vertices meet the end condition, so running is false.
            If some of them does not, running is set to true later in the code. */
            running = 0;
        } else {
            /* Shuffle the node ordering vector if we are in the label updating iteration */
            IGRAPH_CHECK(igraph_vector_shuffle(&node_order));
        }
    }

    /* In the prescribed order, loop over the vertices and reassign labels */
    for (i = 0; i < no_of_not_fixed_nodes; i++) {
      v1 = (long int) VECTOR(node_order)[i];

      /* Count the weights corresponding to different labels */
      igraph_vector_clear(&dominant_labels);
      igraph_vector_clear(&nonzero_labels);
      max_count = 0.0;
      if (weights) {
        ineis = igraph_inclist_get(&il, v1);
        num_neis = igraph_vector_int_size(ineis);
        for (j = 0; j < num_neis; j++) {
          k = (long int) VECTOR(*membership)[
              (long)IGRAPH_OTHER(graph, VECTOR(*ineis)[j], v1) ];
          if (k < 0) {
            continue;    /* skip if it has no label yet */
          }
          was_zero = (VECTOR(label_counters)[k] == 0);
          VECTOR(label_counters)[k] += VECTOR(*weights)[(long)VECTOR(*ineis)[j]];
          if (was_zero && VECTOR(label_counters)[k] != 0) {
            /* counter just became nonzero */
            IGRAPH_CHECK(igraph_vector_push_back(&nonzero_labels, k));
          }
          if (max_count < VECTOR(label_counters)[k]) {
            max_count = VECTOR(label_counters)[k];
            IGRAPH_CHECK(igraph_vector_resize(&dominant_labels, 1));
            VECTOR(dominant_labels)[0] = k;
          } else if (max_count == VECTOR(label_counters)[k]) {
            IGRAPH_CHECK(igraph_vector_push_back(&dominant_labels, k));
          }
        }
      } else {
        neis = igraph_adjlist_get(&al, v1);
        num_neis = igraph_vector_int_size(neis);
        for (j = 0; j < num_neis; j++) {
          k = (long int) VECTOR(*membership)[(long)VECTOR(*neis)[j]];
          if (k < 0) {
            continue;    /* skip if it has no label yet */
          }
          VECTOR(label_counters)[k]++;
          if (VECTOR(label_counters)[k] == 1) {
            /* counter just became nonzero */
            IGRAPH_CHECK(igraph_vector_push_back(&nonzero_labels, k));
          }
          if (max_count < VECTOR(label_counters)[k]) {
            max_count = VECTOR(label_counters)[k];
            IGRAPH_CHECK(igraph_vector_resize(&dominant_labels, 1));
            VECTOR(dominant_labels)[0] = k;
          } else if (max_count == VECTOR(label_counters)[k]) {
            IGRAPH_CHECK(igraph_vector_push_back(&dominant_labels, k));
          }
        }
      }

      if (igraph_vector_size(&dominant_labels) > 0) {
        if (retention) {
            /* If we are using retention, we first check if the current label
               is among the maximum label. */
            j = (long)VECTOR(*membership)[v1];
            if (j < 0 || /* Doesn't have a label yet */
                VECTOR(label_counters)[j] == 0 || /* Label not present in neighbors */
                VECTOR(label_counters)[j] < max_count /* Label not dominant */
               )
            {
                /* Select randomly from the dominant labels */
                k = RNG_INTEGER(0, igraph_vector_size(&dominant_labels) - 1);
                k = VECTOR(dominant_labels)[(long int)k];
                /* If label changes, we will continue running */
                if (k != j)
                    running = 1;
                /* Actually change label */
                VECTOR(*membership)[v1] = k;
            }
        }
        else {
            /* We are not using retention, so check if we should do a control iteration
               or an update iteration. */
            if (control_iteration) {
                /* Check if the _current_ label of the node is also dominant */
                if (VECTOR(label_counters)[(long)VECTOR(*membership)[v1]] < max_count) {
                    /* Nope, we need at least one more iteration */
                    running = 1;
                }
            }
            else {
                /* Select randomly from the dominant labels */
                k = RNG_INTEGER(0, igraph_vector_size(&dominant_labels) - 1);
                VECTOR(*membership)[v1] = VECTOR(dominant_labels)[(long int)k];
            }
        }

      }

      /* Clear the nonzero elements in label_counters */
      num_neis = igraph_vector_size(&nonzero_labels);
      for (j = 0; j < num_neis; j++) {
        VECTOR(label_counters)[(long int)VECTOR(nonzero_labels)[j]] = 0;
      }
    }

    /* Alternating between control iterations and label updating iterations */
    if (!retention)
        control_iteration = !control_iteration;
  }

  RNG_END();

  if (weights) {
    igraph_inclist_destroy(&il);
  } else {
    igraph_adjlist_destroy(&al);
  }
  IGRAPH_FINALLY_CLEAN(1);

  igraph_vector_destroy(&node_order);
  igraph_vector_destroy(&label_counters);
  igraph_vector_destroy(&dominant_labels);
  igraph_vector_destroy(&nonzero_labels);
  IGRAPH_FINALLY_CLEAN(4);

  return IGRAPH_SUCCESS;
}

#define DEFAULT_WEIGTH 1
#define SEED_WEIGTH 2


int igraph_i_community_ck_label_propagation(const igraph_t *graph,
    igraph_vector_t *membership,
    const igraph_vector_t *weights,
    igraph_vector_bool_t *fixed,
    igraph_bool_t retention)
{
  long int no_of_nodes = igraph_vcount(graph);
  long int no_of_not_fixed_nodes = 0;
  long int i, j, k;
  igraph_adjlist_t al;
  igraph_inclist_t il;
  igraph_bool_t running, control_iteration;
  igraph_vector_t label_counters, dominant_labels, nonzero_labels, node_order;
  
  // vtx weight (double)
  igraph_vector_t vertex_weight; 
  IGRAPH_VECTOR_INIT_FINALLY(&vertex_weight, no_of_nodes);

  igraph_dqueue_t queue;    // this is a queue where we can add elements to the beggining /end 
  igraph_vector_bool_t in_queue;

  IGRAPH_CHECK(igraph_dqueue_init(&queue, no_of_nodes));
  IGRAPH_FINALLY(igraph_dqueue_destroy, &queue);
  IGRAPH_VECTOR_BOOL_INIT_FINALLY(&in_queue, no_of_nodes);

  /* Create an adjacency/incidence list representation for efficiency.
   * For the unweighted case, the adjacency list is enough. For the
   * weighted case, we need the incidence list */
  // if (weights) {
    // IGRAPH_CHECK(igraph_inclist_init(graph, &il, IGRAPH_IN, IGRAPH_LOOPS_ONCE));
    // IGRAPH_FINALLY(igraph_inclist_destroy, &il);
  // } else {
    IGRAPH_CHECK(igraph_adjlist_init(graph, &al, IGRAPH_IN, IGRAPH_LOOPS_ONCE, IGRAPH_MULTIPLE));
    IGRAPH_FINALLY(igraph_adjlist_destroy, &al);
  // }

  /* Create storage space for counting distinct labels and dominant ones */
  IGRAPH_VECTOR_INIT_FINALLY(&label_counters, no_of_nodes);
  IGRAPH_VECTOR_INIT_FINALLY(&dominant_labels, 0);
  IGRAPH_VECTOR_INIT_FINALLY(&nonzero_labels, 0);
  IGRAPH_CHECK(igraph_vector_reserve(&dominant_labels, 2));

  /* Initialize node ordering vector with only the not fixed nodes */
  IGRAPH_CHECK(igraph_vector_init_seq(&node_order, 0, no_of_nodes - 1));
  IGRAPH_FINALLY(igraph_vector_destroy, &node_order);
  no_of_not_fixed_nodes = no_of_nodes;

  RNG_BEGIN();
  
  /*  0. Set labels to 0  */ // Not needed ? 

  /*  1. FIND COMMUNITY SEEDS 
  *   1.1.  Order nodes by degree  
  *   1.2.  Use ordered node list -> select 1st nodes with highest degree & disconnected 
  *   1.3.  Label those nodes with their own communities (each one = center of a unique community)
  */
  clock_t start, end;
  double cpu_time_used;
     
  start = clock();
  igraph_vector_t degrees;
  igraph_vector_init(&degrees, no_of_nodes);

  // get all degrees of vtx 
  igraph_degree(graph, &degrees, igraph_vss_all(), IGRAPH_ALL, IGRAPH_NO_LOOPS);   
  // order nodes from higher to lower degree
  igraph_vector_qsort_ind(&degrees, &node_order, IGRAPH_DESCENDING); 
  
  end = clock();
  cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
  printf("Time for ordering by degree: %f seconds\n", (double)cpu_time_used);
  // i dont need this anymore 
  // igraph_vector_destroy(&degrees);

  // 1.2) Use ordered node list -> select 1st nodes with highest degree & disconnected 
  // set the number of communities, this should be passed as a parameter 
  int num_seeds = 	75149; //227166 //zackary:2 //dolphins:4   //dblp:13477 //amazon:75149         // PARAMETER 
  int found_communities = 1;  
  int candidate = 0; 
  int max_degree = (long int)VECTOR(node_order)[candidate]; // degree 1st node (from ordered list)

  // if there are no seeds to find -> end 
  if(num_seeds <= 0) return 0;  
  
  start = clock();
  igraph_vector_t seed_neighbors, community_core_candidate, no_core, seed_nodes, candidate_neigbors, nodes_to_append, test;
  igraph_vector_init(&seed_neighbors, 0);
  igraph_vector_init(&community_core_candidate, no_of_nodes);
  igraph_vector_init(&no_core, no_of_nodes);
  igraph_vector_init(&test, 0);
  igraph_vector_init(&seed_nodes, num_seeds);
  igraph_vector_fill(&seed_nodes, 1);
  igraph_vector_init(&candidate_neigbors, 0);
  igraph_vector_init(&nodes_to_append, 0);
  igraph_vector_fill(&label_counters, 0); 

  // first node is always a seed 
  // no need to add to queue as we work with seed_nodes vector 
  VECTOR(*membership)[(long int)VECTOR(node_order)[candidate]] = 0; 
  VECTOR(vertex_weight)[(long int)VECTOR(node_order)[candidate]] = DEFAULT_WEIGTH + SEED_WEIGTH + 1; // 1 = deg/max(deg)

  // add 1st node neighborst to seed_neighbors (cadidate vtx for community cores)
  VECTOR(seed_nodes)[0] = (long int)VECTOR(node_order)[candidate]; 
  igraph_neighbors(graph, &seed_neighbors, VECTOR(node_order)[candidate], IGRAPH_ALL); 
  for(int i=0; i<igraph_vector_size(&seed_neighbors); i++){
    int v = VECTOR(seed_neighbors)[i];
    VECTOR(label_counters)[v] = VECTOR(label_counters)[v]+1;   
    // printf("Added +1 to my neighbor %d with value %f\n", v, VECTOR(label_counters)[v]);
  }

  candidate++; 

  //////////////////////////////////////////////////////// REVISANDO /////////////////////////////////////////////////////////////////////////
  ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  // here idk which nodes are seeds yet so i cannot append the neighbors of a seed to the queue and set as community cores
  // until we find all the seeds or we do a pass in all the nodes  
  while(found_communities < num_seeds && candidate < no_of_nodes)
  {
    igraph_vector_clear(&candidate_neigbors);
    igraph_vector_clear(&test);

    // get neighbors of next candidate seed 
    long int candidate_seed = VECTOR(node_order)[candidate];
    igraph_neighbors(graph, &candidate_neigbors, candidate_seed, IGRAPH_ALL); 
    
    int found = 0; 
    // printf("Neighbors of candidate seed %d : ", (int)candidate_seed);
    // compare the neighbors with the current list seed(s)
    for(long int i=0; i<found_communities; i++){
      // printf("%d ", (int)VECTOR(candidate_neigbors)[i]);
      if(igraph_vector_contains(&candidate_neigbors, VECTOR(seed_nodes)[i]) ){
        found = 1; 
        break;
      }
    }
    candidate++; 

    // if there is no neighbort that is a seed -> node (seed candidate) = seed 
    if(found) continue; 
    
    // add new seed to community vector of seed nodes 
    VECTOR(seed_nodes)[found_communities] = candidate_seed;   // add to seed nodes 

    // add label and weight to community seed 
    VECTOR(*membership)[candidate_seed] = found_communities; // add label to new community 
    VECTOR(vertex_weight)[candidate_seed] = DEFAULT_WEIGTH + SEED_WEIGTH + 1;  // we're still adding se

    // if(found_communities==1){
    // printf("I'm seed %d with community label %d and weight %f\n", (int)candidate_seed, found_communities, VECTOR(vertex_weight)[candidate_seed]);
    for(int i=0; i<igraph_vector_size(&candidate_neigbors); i++){
      int v = VECTOR(candidate_neigbors)[i];
      VECTOR(label_counters)[v] = VECTOR(label_counters)[v]+1;   
      // printf("Added +1 to my [%d] neighbor %d with value %f\n", candidate_seed, v, VECTOR(label_counters)[v]);
    }
    // }
    

    found_communities++; 
  }

  end = clock();
  cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
  printf("Time for finding %d community seeds: %f seconds\n", found_communities, (double)cpu_time_used);

  int cnt_core = 0, cnt_no_core =0; 
  start = clock();
  for(int i=0; i<no_of_nodes; i++){
    // printf("I'm node %d with nº label value : %d\n", i, (long int)VECTOR(label_counters)[i]); 
    if((long int)VECTOR(label_counters)[i] <= 0){
      continue;
    }
    if((long int)VECTOR(label_counters)[i] == 1){
      // printf("I'm a CORE node %d at %d with nº labels : %d\n", i, cnt_core, (int)VECTOR(label_counters)[i]); 
      VECTOR(community_core_candidate)[cnt_core] = i;
      // VECTOR(in_queue)[i] == 1; 
      cnt_core++; 
    } else if((long int)VECTOR(label_counters)[i] > 1){
      // printf("I'm node %d with nº labels : %d\n", i, (int)VECTOR(label_counters)[i]); 
      VECTOR(no_core)[cnt_no_core] = i;
      // VECTOR(in_queue)[i] == 1; 
      cnt_no_core++;
    }    
  }
  // reset labels + queue 
  igraph_vector_fill(&in_queue, 0); 
  igraph_vector_fill(&label_counters, 0); 

  end = clock();
  cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
  printf("Time for finding CORES: %f seconds\n", (double)cpu_time_used);
  
  start = clock();

  // need to resize to proper size before sorting -> avoid 0s if not resized 
  igraph_vector_resize(&community_core_candidate, cnt_core);
  igraph_vector_resize(&no_core, cnt_no_core);

  igraph_vector_sort(&no_core);
  igraph_vector_sort(&community_core_candidate); 

  for(int i=0; i<found_communities; i++){
    //get neighbors of seed 
    long int seed = VECTOR(seed_nodes)[i];
    igraph_neighbors(graph, &seed_neighbors, seed, IGRAPH_ALL); 

    // get cores belong to seed 
    igraph_vector_intersect_sorted(&community_core_candidate, &seed_neighbors, &nodes_to_append);

    // update label/weight of cores 
    for(int j=0; j<igraph_vector_size(&nodes_to_append); j++){
      long int v = VECTOR(nodes_to_append)[j];
      VECTOR(*membership)[v] = VECTOR(*membership)[seed]; // add label to new community 
      VECTOR(vertex_weight)[v] = DEFAULT_WEIGTH + 0.5 + ((double)VECTOR(degrees)[v]/(double)max_degree);  // we're still adding seeds 
    }
  }

  // get no cores into queue + set weight    
  for(int j=0; j<cnt_no_core; j++){
    long int v = VECTOR(no_core)[j];

    igraph_dqueue_push(&queue, v); // add unlabeled node to queue 
    VECTOR(in_queue)[v] = 1; 
    VECTOR(vertex_weight)[v] = DEFAULT_WEIGTH + 0.5 + 1;  // we're still adding seeds 
  }

  // add unlabeled neighbors of cores to queue 
  for(int i=0; i<cnt_core; i++){
    // get neighbors of core 
    long int cc = VECTOR(community_core_candidate)[i];
    igraph_neighbors(graph, &seed_neighbors, cc, IGRAPH_ALL); 

    // put in queue any neighbor not labeled and not in queue 
    for(int j=0; j<igraph_vector_size(&seed_neighbors); j++){
      long int v = VECTOR(seed_neighbors)[j];
      if(!VECTOR(in_queue)[v] && VECTOR(*membership)[v] < 0){
        igraph_dqueue_push(&queue, v);
        VECTOR(in_queue)[v] = 1; 
      }
    }
  }

  end = clock();
  cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
  printf("Time for setting core labels + queue: %f seconds\n", (double)cpu_time_used);

  igraph_vector_destroy(&seed_neighbors);
  igraph_vector_destroy(&community_core_candidate);
  igraph_vector_destroy(&no_core);

  
  // /*  3. FIND COMMUNITIES -- run LPA 
  // *   3.1.  For all nodes in queue -> run LPA  
  // *   3.2.  get sum of weight for all labels 
  // *   3.3.  max(weight) -> newLabel 
  // *                     draw -> break tie in favor highest label (not rng) 
  // */

  start = clock();
  int wave = 2; 
  int nodes_should_be_assigned = 0;
  int cnt = igraph_dqueue_size(&queue); 
  while (!igraph_dqueue_empty(&queue)) {
    long int v1, v2, e = -1, num_neis;
    igraph_real_t max_count;
    igraph_vector_int_t *neis;
    igraph_bool_t was_zero;

    // saca 1r elemento cola 
    v1 = igraph_dqueue_pop(&queue);
    VECTOR(in_queue)[v1] = 0;       // marca que ya no esta en la cola 

    // vacia dominant_labels y nonzero
    igraph_vector_clear(&dominant_labels);
    igraph_vector_clear(&nonzero_labels);
    max_count = 0.0;

    // saca vecinos de nodo a labear 
    neis = igraph_adjlist_get(&al, v1);

    // nº vecinos = degree 
    num_neis = igraph_vector_int_size(neis);
    // this looks for the maximum label(s) - in our case by max weight 
    // para cada vecino 
    for (j = 0; j < num_neis; j++) {
      // saca nº vecino 
      v2 = (long int)VECTOR(*neis)[j];
      // saca label vecino
      k = (long int)VECTOR(*membership)[v2];

      // si aun no tiene label -> ignora el vecino -> siguiente 
      if (k < 0) 
        continue;    /* skip if it has no label yet */

      // si para esa estiqueta que tiene el vecino no hay ningun valor [was_zero = 1]
      was_zero = (VECTOR(label_counters)[k] == 0);

      // a label_counters[k] se le suma el valor del peso de ese vecino 
      VECTOR(label_counters)[k] +=  VECTOR(vertex_weight)[v2];

      // si antes no habia valores para esa etiqueta y ahora si -> se marca etiqueta como nonzero
      if (was_zero && VECTOR(label_counters)[k] >= 0) {
        /* counter just became non-negative */
        IGRAPH_CHECK(igraph_vector_push_back(&nonzero_labels, k));
      }
      // si el valor maximo hasta ahora es menor que el valor de la etiqueta actual 
      if (max_count < VECTOR(label_counters)[k]) {
        // se actualiza el valor maximo
        max_count = VECTOR(label_counters)[k];

        // se añade devuelve a size=1 dominant_labels y se mete la etiqueta que toca 
        IGRAPH_CHECK(igraph_vector_resize(&dominant_labels, 1));
        VECTOR(dominant_labels)[0] = k;

        // si el valor de la etiqueta es = a el que ya hay de maximo -> se añade a las etiquetas maximas 
      } else if (max_count == VECTOR(label_counters)[k]) {
        IGRAPH_CHECK(igraph_vector_push_back(&dominant_labels, k));
      }
    }
    
    // si el nº de etiquetas maximas es > 0 
    // if (igraph_vector_size(&dominant_labels) > 0) {
      // se saca la etiqueta actual 
      long current_label = (long)VECTOR(*membership)[v1];

      /* Select max label */
      k = igraph_vector_which_max(&dominant_labels);
      long new_label = (long int) VECTOR(dominant_labels)[k];

      /* We still need to consider its neighbors not in the new community */
      // para todos los vecinos del vtx a evaluar 
      for (j = 0; j < num_neis; j++) {  
        //update queue with unlabeled neighbors (that are NOT currently in the queue)
        v2 = (long int)VECTOR(*neis)[j];
        igraph_integer_t neigh_label = (long int) VECTOR(*membership)[v2]; /* neighbor community */

        // as long as neighbor is not in the queue AND its NOT labeled 
        if (!VECTOR(in_queue)[v2] && neigh_label < 0){
          // printf("Add neighbor %d to the queue \n", (int)v2);
          igraph_dqueue_push(&queue, v2);
          VECTOR(in_queue)[v2] = 1;
        }
      }

      // se actualiza la etiqueta del vtx actual 
      VECTOR(*membership)[v1] = new_label;
      // si el peso < 0 (siempre??) -> actualiza el peso 
      if(VECTOR(vertex_weight)[v1] < 0){
        double w3 = (VECTOR(degrees)[v1]/max_degree)  ;
        VECTOR(vertex_weight)[v1] = DEFAULT_WEIGTH + pow(0.5,wave) + w3;
      } 
    // }

    /* Clear the nonzero elements in label_counters */
    num_neis = igraph_vector_size(&nonzero_labels);
    // para todas las etiquetas = non son zero  
    for (j = 0; j < num_neis; j++) {
      // en contador de etiquetas se asigna 0 a label_counters  
      VECTOR(label_counters)[(long int)VECTOR(nonzero_labels)[j]] = 0;
    }

    // change wave when we do a pass to the queue 
    cnt--;
    if (cnt == 0) {cnt = igraph_dqueue_size(&queue); wave++;}
    nodes_should_be_assigned++; 
  }

  end = clock();
  cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
  printf("Time for LPA: %f seconds and number of iterations %d [assigning %d nodes]\n", (double)cpu_time_used, wave-2, nodes_should_be_assigned);

  // if (weights) {
  //   igraph_inclist_destroy(&il);
  // } else {
    igraph_adjlist_destroy(&al);
  // }

  IGRAPH_FINALLY_CLEAN(1);

  igraph_vector_destroy(&node_order);
  igraph_vector_destroy(&label_counters);
  igraph_vector_destroy(&dominant_labels);
  igraph_vector_destroy(&nonzero_labels);
  IGRAPH_FINALLY_CLEAN(4);

  return IGRAPH_SUCCESS;
}


// FOR DEBUG 
void print_vector(igraph_vector_t *v, FILE *f) {
    long int i;
    for (i = 0; i < igraph_vector_size(v); i++) {
        fprintf(f, " %.2f", VECTOR(*v)[i]);
    }
    fprintf(f, "\n");
}

#define DEFAULT_WEIGTH 1
#define SEED_WEIGTH 2


int igraph_i_community_dpc_label_propagation(const igraph_t *graph,
    igraph_vector_t *membership,
    const igraph_vector_t *weights,
    igraph_vector_bool_t *fixed,
    igraph_bool_t retention)
{
  long int no_of_nodes = igraph_vcount(graph);
  long int no_of_not_fixed_nodes = 0;
  long int i, j, k;
  igraph_adjlist_t al;
  igraph_inclist_t il;
  igraph_bool_t running, control_iteration;
  igraph_vector_t label_counters, dominant_labels, nonzero_labels, node_order;
  
  // vtx weight (double)
  igraph_vector_t vertex_quality, vertex_density, centrality_index, h, diff_h; 
  igraph_vector_init(&vertex_quality, no_of_nodes);
  igraph_vector_init(&vertex_density, no_of_nodes);
  igraph_vector_init(&centrality_index, no_of_nodes);
  igraph_vector_init(&h, no_of_nodes);
  igraph_vector_init(&diff_h, no_of_nodes);

  // igraph_vector_t vertex_weight; 
  // IGRAPH_VECTOR_INIT_FINALLY(&vertex_weight, no_of_nodes);

  // IGRAPH_VECTOR_INIT_FINALLY(&vertex_quality, no_of_nodes);
  // IGRAPH_VECTOR_INIT_FINALLY(&vertex_quality, no_of_nodes);
  // IGRAPH_VECTOR_INIT_FINALLY(&centrality_index, no_of_nodes);
  // IGRAPH_VECTOR_INIT_FINALLY(&h, no_of_nodes);

  igraph_dqueue_t queue;    // this is a queue where we can add elements to the beggining /end 
  igraph_vector_bool_t in_queue;

  IGRAPH_CHECK(igraph_dqueue_init(&queue, no_of_nodes));
  IGRAPH_FINALLY(igraph_dqueue_destroy, &queue);
  IGRAPH_VECTOR_BOOL_INIT_FINALLY(&in_queue, no_of_nodes);

  /* Create an adjacency/incidence list representation for efficiency.
   * For the unweighted case, the adjacency list is enough. For the
   * weighted case, we need the incidence list */
  IGRAPH_CHECK(igraph_adjlist_init(graph, &al, IGRAPH_IN, IGRAPH_LOOPS_ONCE, IGRAPH_MULTIPLE));
  IGRAPH_FINALLY(igraph_adjlist_destroy, &al);

  /* Create storage space for counting distinct labels and dominant ones */
  IGRAPH_VECTOR_INIT_FINALLY(&label_counters, no_of_nodes);
  IGRAPH_VECTOR_INIT_FINALLY(&dominant_labels, 0);
  IGRAPH_VECTOR_INIT_FINALLY(&nonzero_labels, 0);
  IGRAPH_CHECK(igraph_vector_reserve(&dominant_labels, 2));

  /* Initialize node ordering vector with only the not fixed nodes */
  IGRAPH_CHECK(igraph_vector_init_seq(&node_order, 0, no_of_nodes - 1));
  IGRAPH_FINALLY(igraph_vector_destroy, &node_order);
  no_of_not_fixed_nodes = no_of_nodes;

  // RNG_BEGIN();

  /* ////////////////////////////////////   DPC + LPA     ////////////////////////////////////
  *  //// Steps 
  *  //// 1. Graph Compression -- Paso de esto x ahora TO DO --
  *       //// 1.1. First Phase 
  *            //// 1.1.1. Search 1 degree vtx & attach to neighbor (run until no more 1st deg vtx)
  *       //// 1.2. Second Phase         
  *            //// 1.2.1. Search 2 degree vtx & attach to highest degree neighbor (run until no more 2nd deg vtx)
  *  //// 2. Finding Centers 
  *       //// 2.1. Calculate quality + density of nodes 
  *       //// 2.2. Normalize values 
  *       //// 2.3. Calculate index with quality / density 
  *       //// 2.4. Order index + select highest knee-point 
  *       //// 2.5. Get all nodes (seeds) below knee-point -> Community seeds obtained 
  *  //// 3. Seed Expansion 
  *       //// 3.1. get neighbors of labeled vtx 
  *       //// 3.2. Label if possible + go back to 3.1 until no more vtx to label  
  *                 //// In case of tie -> break with similarity measure (neighborhood/Jaccard/other?)
  *       //// 3.x. Expand to compressed graph  
  */
  //////////////////////////////////////////////////////////
  /*  1. Graph Compression  */
  //////////////////////////////////////////////////////////

  // igraph_vector_int_t degree1_vtx, degree2_vtx, vertex_weight;
  // igraph_dqueue_t degree1_queue, degree2_queue;    // this is a queue where we can add elements to the beggining /end 
  // // igraph_vector_t vertex_weight; 

  // IGRAPH_CHECK(igraph_dqueue_init(&degree1_queue, no_of_nodes));
  // IGRAPH_FINALLY(igraph_dqueue_destroy, &degree1_queue);

  // IGRAPH_CHECK(igraph_dqueue_init(&degree2_queue, no_of_nodes));
  // IGRAPH_FINALLY(igraph_dqueue_destroy, &degree2_queue);

  // igraph_vector_int_init(&degree1_vtx, no_of_nodes);
  // igraph_vector_int_init(&degree2_vtx, no_of_nodes);
  // igraph_vector_int_init(&vertex_weight, no_of_nodes);
  // igraph_vector_fill(&vertex_weight, 1);

  // // copy graph to compressed graph 
  // igraph_t compressed_graph; 

  // igraph_copy(&compressed_graph, graph); 
  
  
  // /* order vtx by degree (increasing order) */
  //   // get all degrees 
  // igraph_degree(graph, &vertex_density, igraph_vss_all(), IGRAPH_ALL, IGRAPH_NO_LOOPS);   
  //   // order degrees 

  // // get the order of the nodes in ascending degree 
  // igraph_vector_qsort_ind(&vertex_density, &node_order, IGRAPH_ASCENDING); 
  // printf("Ordered To follow : ");
  // print_vector(&node_order, stdout);
  // printf("\n");

  //   // order nodes by degree 
  // igraph_vector_sort(&vertex_density);  
  // printf("Ordered Degrees: ");
  // print_vector(&vertex_density, stdout);
  // printf("\n");

  // // fill degree arrays 
  // long int aux = 0, curr_deg, d1=0, d2=0; 
  // do
  // {
  //   curr_deg = (long int) VECTOR(vertex_density)[aux]; 
  //   printf("Evaluating current degree at %d\n", curr_deg); 
  //   if(curr_deg == 1){
  //     VECTOR(degree1_vtx)[d1] = (long int) VECTOR(node_order)[aux];
  //     d1++;
  //   }else if (curr_deg < 3){
  //     VECTOR(degree2_vtx)[d2] = (long int) VECTOR(node_order)[aux];
  //     d2++; 
  //   }
  //   aux++;
  // }while(curr_deg < 3 && aux<no_of_nodes);

  // printf("Found a total of %d nº before degree 3\n", aux); 
  
  // // resize vectors to its current size 
  // igraph_vector_resize(&degree1_vtx, d1);
  // igraph_vector_resize(&degree2_vtx, d2);

  // // printf("Degree 1 vtx: ");
  // // for(int i=0; i<d1; i++){
  // //   printf("%d ", VECTOR(degree1_vtx)[i]);
  // // }
  // // printf("\n");

  // // printf("Degree 2 vtx: ");
  // // for(int i=0; i<d2; i++){
  // //   printf("%d ", VECTOR(degree2_vtx)[i]);
  // // }
  // // printf("\n");

  // // Perform graph compression 
  // int socorro=0;
  // // do{
  //   // evaluate degree 1 nodes 

  // igraph_vector_t d1_indices;
  // igraph_vector_init(&d1_indices, 0);
  // while(){

  // }


  // // for(int i=0; i<igraph_vector_size(&degree1_vtx); i++){
  // //   // add vtx to rmv list 
  // //   igraph_vector_push_back(&indices, VECTOR(degree1_vtx)[i]);
  // //   // store vtx value 

  // //   // update the weight of the new vtx 

  // // }
  // // remove degree1 vtx from compressed 
  // igraph_delete_vertices(compressed_graph, igraph_vss_vector(&d1_indices))

  //   socorro++;
  // // }while((igraph_vector_int_size() != 0 && igraph_vector_size() != 0) || socorro < 10)

  // igraph_vector_int_destroy(&degree1_vtx);
  // igraph_vector_int_destroy(&degree2_vtx);
  // igraph_destroy(&compressed_graph);


  //////////////////////////////////////////////////////////
  /*  2. Finding Centers  */
  //////////////////////////////////////////////////////////

  /*  2.1. Calculate quality + density of nodes */
  // get degree of all nodes  
  igraph_degree(graph, &vertex_density, igraph_vss_all(), IGRAPH_ALL, IGRAPH_NO_LOOPS);   
  // printf("Vector of density : ");
  // print_vector(&vertex_density, stdout);
  // printf("\n");

  // get max degree (store in quality array)
  igraph_integer_t mdeg; 
  igraph_maxdegree(graph, &mdeg, igraph_vss_all(), IGRAPH_ALL, IGRAPH_LOOPS);
  printf("MAX_DEGREE : %d\n", mdeg); 

  /*  2.2. Normalize values */
  // normalize value of density (multiply by 1/maxdegree)
  igraph_vector_scale(&vertex_density, (double)1/(double)mdeg);
  printf("Vector of normalized density : ");
  print_vector(&vertex_density, stdout);

  // set quality to its value ----------------------------
  igraph_vector_fill(&vertex_quality, 1);  // should be the weight of the node, not 1 -------

  // EXAMPLE: Load by hand the (normalised) quality of the example graph : 
  // VECTOR(vertex_quality)[0] = 1.0/4.0;
  // VECTOR(vertex_quality)[1] = 1.0/4.0;
  // VECTOR(vertex_quality)[2] = 1.0/4.0;
  // VECTOR(vertex_quality)[3] = 3.0/4.0;
  // VECTOR(vertex_quality)[4] = 1.0/4.0;
  // VECTOR(vertex_quality)[5] = 1.0/4.0;
  // VECTOR(vertex_quality)[6] = 4.0/4.0;
  // VECTOR(vertex_quality)[7] = 1.0/4.0;
  // VECTOR(vertex_quality)[8] = 1.0/4.0;
  // VECTOR(vertex_quality)[9] = 1.0/4.0;

  // int max_quality = 4; 
  printf("Vector of normalized quality : ");
  print_vector(&vertex_quality, stdout);
  // ----------------------------------------------------- CHANGE LATER <- (above code)

  //// 2.3. Calculate index with quality / density 
  // copy density vector 
  // igraph_vector_init_copy
  igraph_vector_copy(&centrality_index, &vertex_density); // deprecated ? igraph_vector_copy should be used ??

  /* 2.4. Order index + select highest knee-point  */
  // calculate centrality index[v] = density'/quality'
  // igraph_vector_div(&centrality_index, &vertex_quality);
  igraph_vector_mul(&centrality_index, &vertex_quality);
  printf("Centrality index : ");
  print_vector(&centrality_index, stdout);
  printf("\n");

  // order vector of centrality (get g1,g2,..,gn) 
  igraph_vector_t inds;
  igraph_vector_init(&inds, no_of_nodes);
  // get the order from higher to lower value -> keep ordering indexes so we can go back
  igraph_vector_qsort_ind(&centrality_index, &inds, IGRAPH_DESCENDING); 
  printf("Ordered To follow : ");
  print_vector(&inds, stdout);
  printf("\n");

  igraph_vector_reverse_sort(&centrality_index);  
  // igraph_vector_permute // Esto no va, sabe nadie pq <- pero se puede hacer con vector_reverse_sort aunq parece + cutre tbh
  // igraph_vector_list_permute(&centrality_index, &inds); // order -- rmv bc i need to keep indexes 
  printf("Ordered centrality index : ");
  print_vector(&centrality_index, stdout);
  printf("\n");

  // calculate 2nd order difference (h) -> hi = |(gi − gi+1) − (gi+1 − gi+2)|
  for(int i=0; i<no_of_nodes-2; i++){
    VECTOR(h)[i] = fabs((VECTOR(centrality_index)[i] - VECTOR(centrality_index)[i+1]) - (VECTOR(centrality_index)[i+1] - VECTOR(centrality_index)[i+2])); 
  }
  printf("h : ");
  print_vector(&h, stdout);
  printf("\n");

  // Calculate the knee-point (argmax(h) -> max differene between two consecutive points of h) 
  // for(int i=0; i<no_of_nodes-2; i++){
  //   VECTOR(diff_h)[i] = fabs((VECTOR(h)[i]-VECTOR(h)[i+1]) - (VECTOR(h)[i+1]-VECTOR(h)[i+2]));
  // }
  // printf("diff_h : ");
  // print_vector(&diff_h, stdout);
  // printf("\n");

  // // i keep 1st max on diff_h -> any node lower than this one is a seed  
  //   // esta mal seguramente ? hay que mantener el 1r punto maximo, puede haber maximos debajo
  igraph_integer_t knee_point = igraph_vector_which_max(&h); // if max element is not unique -> 1st index is returned

  // igraph_integer_t knee_point = 4; 
  printf("MAX INDEX : %d\n", knee_point); 
  // https://stackoverflow.com/questions/4471993/compute-the-elbow-for-a-curve-automatically-and-mathematically ?

  /*  2.5. Get all nodes (seeds) below knee-point -> Community seeds obtained */
  // we have the index of the knee point -> any vtx above knee point = community seed 
  // int found_seeds = 0; 
  // for(int i=0; i<=knee_point; i++){
  //   // printf("Node %ld is a candidate to community seed\n", (long int)VECTOR(inds)[i]); 
  //   // put node into queue 
  //   igraph_dqueue_push(&queue, (long int)VECTOR(inds)[i]);

  //   // WIP -- NEED TO CHECK TO MAKE SURE SEEDS != NEIGHBORS <- 
  //   VECTOR(*membership)[(long int)VECTOR(inds)[i]] = found_seeds; // add label of the community 
  //   VECTOR(in_queue)[(long int)VECTOR(inds)[i]] = 1;    // set the element in queue = true 
  //   VECTOR(vertex_weight)[(long int)VECTOR(inds)[i]] = DEFAULT_WEIGTH + SEED_WEIGTH + 1; // set weight of seeds 
  //   found_seeds++; // community label = updated 
  // }

  // // printf("There should be %d communities and we found %d\n", knee_point,found_seeds); 
  /* delete values of density / quality -> free */

    // get communities -> all vtx are candidates  

  //////////////////////////////////////////////////////////
  /* 3. Seed Expansion */
  //////////////////////////////////////////////////////////

  ///////////////////////////////////////////// DEBUG /////////////////////////////////////////////
  // // printf("Communities membership before : \n");
  // // for(int i=0; i<no_of_nodes; i++){
  // //   printf("%f ", VECTOR(*membership)[i]); 
  // // }
  // // printf("\n");
  // /////////////////////////////////////////// FIN DEBUG ///////////////////////////////////////////

  // // 1st expand to community cores -> direct neighbors to a single node = belong to that community 
  // igraph_vector_t candidate_neigbors, new_candidate_neigbors, other_comm_neigh;
  // igraph_vector_t neigbors_intersection;
  // igraph_vector_init(&candidate_neigbors, 0);
  // igraph_vector_init(&new_candidate_neigbors, 0);
  // igraph_vector_init(&other_comm_neigh, 0);
  // igraph_vector_init(&neigbors_intersection, 0);

  // // get direct neighbors to seed 
  // for(int i=0; i<found_seeds; i++)
  // {
  //   // 2.1.  Find all neighbors to a single community seed (i)
  //   long int candidate_seed = igraph_dqueue_e(&queue, i);
  //   // get neighbors of a community seed 
  //   igraph_neighbors(graph, &candidate_neigbors, candidate_seed, IGRAPH_ALL); 

  //   // calculates the intersection with other communities 
  //   for(int j=0; j<found_seeds; j++){    
  //     if(j==i) continue; // no need to check if current community has its own neighbors
  //      (graph, &other_comm_neigh,igraph_dqueue_e(&queue, j), IGRAPH_ALL); 
  //     igraph_vector_intersect_sorted(&candidate_neigbors, &other_comm_neigh, &neigbors_intersection);
  //     // keep only the ones that are not in another community 
  //     igraph_vector_difference_sorted(&candidate_neigbors, &neigbors_intersection, &new_candidate_neigbors);
  //   }

  //   // printf("Neighbors of %f added : ", igraph_dqueue_e(&queue, i));
  //   for(int k=0; k<igraph_vector_size(&new_candidate_neigbors); k++){
  //     // printf("Candidate %f JOINS vtx %ld [with label %f]\n", VECTOR(new_candidate_neigbors)[k], candidate_seed, VECTOR(*membership)[candidate_seed]); 
  //     // neighbor to i belongs to i community 
  //     long int k_n = VECTOR(new_candidate_neigbors)[k];

  //     // add neighbors to labeled node to queue 
  //     // igraph_dqueue_push(&queue, k_n); 
      
  //     //   2.2.  Set the weight and label of cores 
  //     VECTOR(*membership)[k_n] = VECTOR(*membership)[candidate_seed];
      
  //     const igraph_vector_int_t *n = igraph_adjlist_get(&al, k_n);
  //     double degree = igraph_vector_int_size(n);
  //     // degree =  DEFAULT_WEIGTH + 0.25 + (double)(degree/max_degree);
  //     // printf("%f [%f] ", VECTOR(new_candidate_neigbors)[k], degree); 

  //     //   2.3.  Rmv seeds from queue + add neighbors of labeled cores  
  //     VECTOR(vertex_weight)[k_n] = DEFAULT_WEIGTH + 0.25 + (double)(degree/mdeg); 
  //   }
  //   // printf("\n");
  // }

  // ///////////////////////////////////////////// DEBUG /////////////////////////////////////////////
  // // printf("CORE communities membership : \n");
  // // for(int i=0; i<no_of_nodes; i++){
  // //   printf("%f ", VECTOR(*membership)[i]); 
  // // }
  // // printf("\n");
  // /////////////////////////////////////////// FIN DEBUG ///////////////////////////////////////////

  // // remove parents from queue as they are no longer needed & add unlabeled childs / childs of childs of seeds 
  // for(int i=0; i<found_seeds; i++){
  //   long int candidate_seed = igraph_dqueue_pop(&queue);
  //   VECTOR(in_queue)[candidate_seed] = 0; // remove element from queue 
  //   igraph_neighbors(graph, &candidate_neigbors, candidate_seed, IGRAPH_ALL); 

  //   for(int j=0; j<igraph_vector_size(&candidate_neigbors); j++){
  //     long int candidate_neighbor = VECTOR(candidate_neigbors)[j];
      
  //     // if neighbor is unlabeled -> add to queue 
  //     if(VECTOR(*membership)[candidate_neighbor] < 0 && VECTOR(in_queue)[candidate_neighbor] == 0){
  //       igraph_dqueue_push(&queue, candidate_neighbor); 
  //       VECTOR(in_queue)[candidate_neighbor] = 1; 
  //       continue; 
  //     }

  //     // if the neighbor is labeled -> check if its neighbors have to be added to the queue 
  //     igraph_neighbors(graph, &new_candidate_neigbors, candidate_neighbor, IGRAPH_ALL); 
  //     for(int k=0; k<igraph_vector_size(&new_candidate_neigbors); k++){
  //       long int n = VECTOR(new_candidate_neigbors)[k];
  //       // if neighbor is unlabeled -> add to queue 
  //       if(VECTOR(*membership)[n] < 0 && VECTOR(in_queue)[n] == 0){
  //         igraph_dqueue_push(&queue, n); 
  //         VECTOR(in_queue)[n] = 1; 
  //       }
  //     }
  //   }
  // }

  // 2nd -> run LPA 
  //  while (!igraph_dqueue_empty(&queue)) {
  //   long int v1, v2, e = -1, num_neis;
  //   igraph_real_t max_count;
  //   igraph_vector_int_t *neis;
  //   igraph_bool_t was_zero;

  //   v1 = igraph_dqueue_pop(&queue);
  //   VECTOR(in_queue)[v1] = 0;

  //   igraph_vector_clear(&dominant_labels);
  //   igraph_vector_clear(&nonzero_labels);
  //   max_count = 0.0;

  //   neis = igraph_adjlist_get(&al, v1);

  //   num_neis = igraph_vector_int_size(neis);
  //   for (j = 0; j < num_neis; j++) {
  //     v2 = (long int)VECTOR(*neis)[j];

  //     k = (long int)VECTOR(*membership)[v2];
  //     if (k < 0) 
  //       continue;    /* skip if it has no label yet */

  //     was_zero = (VECTOR(label_counters)[k] == 0);

  //     // label_counters[k] -> k = label -> accumulates weights k 
  //     VECTOR(label_counters)[k] +=  VECTOR(vertex_weight)[k];

  //     if (was_zero && VECTOR(label_counters)[k] >= 0) {
  //       /* counter just became non-negative */
  //       IGRAPH_CHECK(igraph_vector_push_back(&nonzero_labels, k));
  //     }
  //     if (max_count < VECTOR(label_counters)[k]) {
  //       max_count = VECTOR(label_counters)[k];
  //       IGRAPH_CHECK(igraph_vector_resize(&dominant_labels, 1));
  //       VECTOR(dominant_labels)[0] = k;
  //     } else if (max_count == VECTOR(label_counters)[k]) {
  //       IGRAPH_CHECK(igraph_vector_push_back(&dominant_labels, k));
  //     }
  //   }

  //   if (igraph_vector_size(&dominant_labels) > 0) {
  //     long current_label = (long)VECTOR(*membership)[v1];

  //     /* Select max label */
  //     k = igraph_vector_which_max(&dominant_labels);
  //     long new_label = (long int) VECTOR(dominant_labels)[k];

  //     /* We still need to consider its neighbors not in the new community */
  //     for (j = 0; j < num_neis; j++) {  
  //       //update queue with unlabeled neighbors (that are NOT currently in the queue)
  //       v2 = (long int)VECTOR(*neis)[j];
  //       igraph_integer_t neigh_label = (long int) VECTOR(*membership)[v2]; /* neighbor community */

  //       // as long as neighbor is not in the queue AND its NOT labeled 
  //       if (!VECTOR(in_queue)[v2] && neigh_label < 0){
  //         igraph_dqueue_push(&queue, v2);
  //         VECTOR(in_queue)[v2] = 1;
  //       }
  //     }
  //     VECTOR(*membership)[v1] = new_label;
  //   }

  //   /* Clear the nonzero elements in label_counters */
  //   num_neis = igraph_vector_size(&nonzero_labels);
  //   for (j = 0; j < num_neis; j++) {
  //     VECTOR(label_counters)[(long int)VECTOR(nonzero_labels)[j]] = 0;
  //   }
  // }


  // while(!igraph_dqueue_empty(&queue)) {
  //   long int v1, v2, e = -1, num_neis;
  //   igraph_real_t max_count;
  //   igraph_vector_int_t *neis;
  //   igraph_bool_t was_zero;

  //   v1 = igraph_dqueue_pop(&queue);
  //   VECTOR(in_queue)[v1] = 0;
  
  // } // end LPA 

  //// 3.x. Expand to compressed graph 
        // graph compression is not implemented therefore no expansion is done here <- 

  igraph_adjlist_destroy(&al);

  IGRAPH_FINALLY_CLEAN(1);

  igraph_vector_destroy(&node_order);
  igraph_vector_destroy(&label_counters);
  igraph_vector_destroy(&dominant_labels);
  igraph_vector_destroy(&nonzero_labels);
  IGRAPH_FINALLY_CLEAN(4);

  return IGRAPH_SUCCESS;
}





int igraph_i_community_fast_label_propagation(const igraph_t *graph,
    igraph_vector_t *membership,
    const igraph_vector_t *weights,
    igraph_vector_bool_t *fixed) {

  long int no_of_nodes = igraph_vcount(graph), no_of_not_fixed_nodes;
  long int i, j, k;
  igraph_inclist_t il;
  igraph_adjlist_t al;

  igraph_vector_t label_counters, dominant_labels, nonzero_labels, node_order;
  igraph_dqueue_t queue;
  igraph_vector_bool_t in_queue;

  if (weights) {
    IGRAPH_CHECK(igraph_inclist_init(graph, &il, IGRAPH_IN, IGRAPH_LOOPS_ONCE));
    IGRAPH_FINALLY(igraph_inclist_destroy, &il);
  }
  else {
    IGRAPH_CHECK(igraph_adjlist_init(graph, &al, IGRAPH_IN, IGRAPH_LOOPS_ONCE, IGRAPH_MULTIPLE));
    IGRAPH_FINALLY(igraph_adjlist_destroy, &al);
  }

  /* Create storage space for counting distinct labels and dominant ones */
  IGRAPH_VECTOR_INIT_FINALLY(&label_counters, no_of_nodes + 1);
  IGRAPH_VECTOR_INIT_FINALLY(&dominant_labels, 0);
  IGRAPH_VECTOR_INIT_FINALLY(&nonzero_labels, 0);
  IGRAPH_CHECK(igraph_vector_reserve(&dominant_labels, 2));

  RNG_BEGIN();

  /* Initialize node ordering vector with only the not fixed nodes */
  IGRAPH_CHECK(igraph_dqueue_init(&queue, no_of_nodes));
  IGRAPH_FINALLY(igraph_dqueue_destroy, &queue);
  IGRAPH_VECTOR_BOOL_INIT_FINALLY(&in_queue, no_of_nodes);

  /* Use random node order */
  IGRAPH_VECTOR_INIT_FINALLY(&node_order, 0);
  IGRAPH_CHECK(igraph_vector_reserve(&node_order, no_of_nodes));
  for (i = 0; i < no_of_nodes; i++) {
    if (fixed == NULL || !VECTOR(*fixed)[i])
      IGRAPH_CHECK(igraph_vector_push_back(&node_order, i));
  }
  IGRAPH_CHECK(igraph_vector_shuffle(&node_order));
  no_of_not_fixed_nodes = igraph_vector_size(&node_order);
  for (i = 0; i < no_of_not_fixed_nodes; i++)
  {
    IGRAPH_CHECK(igraph_dqueue_push(&queue, VECTOR(node_order)[i]));
    VECTOR(in_queue)[(igraph_integer_t)VECTOR(node_order)[i]] = 1;
  }
  igraph_vector_destroy(&node_order);
  IGRAPH_FINALLY_CLEAN(1);

  while (!igraph_dqueue_empty(&queue)) {
    long int v1, v2, e = -1, num_neis;
    igraph_real_t max_count;
    igraph_vector_int_t *neis;
    igraph_bool_t was_zero;

    v1 = igraph_dqueue_pop(&queue);
    VECTOR(in_queue)[v1] = 0;

    /* Count the weights corresponding to different labels */
    igraph_vector_clear(&dominant_labels);
    igraph_vector_clear(&nonzero_labels);
    max_count = 0.0;
    if (weights)
      neis = igraph_inclist_get(&il, v1);
    else
      neis = igraph_adjlist_get(&al, v1);

    num_neis = igraph_vector_int_size(neis);
    for (j = 0; j < num_neis; j++) {
      if (weights) {
        e = (long int)VECTOR(*neis)[j];
        v2 = (long int)IGRAPH_OTHER(graph, e, v1);
      }
      else {
        v2 = (long int)VECTOR(*neis)[j];
      }
      k = (long int)VECTOR(*membership)[v2];
      if (k < 0) {
        continue;    /* skip if it has no label yet */
      }
      was_zero = (VECTOR(label_counters)[k] == 0);
      VECTOR(label_counters)[k] += (weights ? VECTOR(*weights)[e] : 1);
      if (was_zero && VECTOR(label_counters)[k] >= 0) {
        /* counter just became non-negative */
        IGRAPH_CHECK(igraph_vector_push_back(&nonzero_labels, k));
      }
      if (max_count < VECTOR(label_counters)[k]) {
        max_count = VECTOR(label_counters)[k];
        IGRAPH_CHECK(igraph_vector_resize(&dominant_labels, 1));
        VECTOR(dominant_labels)[0] = k;
      } else if (max_count == VECTOR(label_counters)[k]) {
        IGRAPH_CHECK(igraph_vector_push_back(&dominant_labels, k));
      }
    }

    if (igraph_vector_size(&dominant_labels) > 0) {
      long current_label = (long)VECTOR(*membership)[v1];

      /* Select randomly from the dominant labels */
      k = RNG_INTEGER(0, igraph_vector_size(&dominant_labels) - 1);
      long new_label = (long int) VECTOR(dominant_labels)[k]; /* a dominant label */

      /* Check if the _current_ label of the node is not the same */
      if (new_label != current_label) {
        /* We still need to consider its neighbors not in the new community */
        for (j = 0; j < num_neis; j++) {
          if (weights) {
            e = (long int)VECTOR(*neis)[j];
            v2 = (long int)IGRAPH_OTHER(graph, e, v1);
          }
          else {
            v2 = (long int)VECTOR(*neis)[j];
          }
          if (!VECTOR(in_queue)[v2])
          {
            igraph_integer_t neigh_label = (long int) VECTOR(*membership)[v2]; /* neighbor community */
            if (neigh_label != new_label && /* not in new community */
                (fixed == NULL || !VECTOR(*fixed)[v2]) ) /* not fixed */ {
              igraph_dqueue_push(&queue, v2);
              VECTOR(in_queue)[v2] = 1;
            }
          }
        }
      }
      VECTOR(*membership)[v1] = new_label;
    }

    /* Clear the nonzero elements in label_counters */
    num_neis = igraph_vector_size(&nonzero_labels);
    for (j = 0; j < num_neis; j++) {
      VECTOR(label_counters)[(long int)VECTOR(nonzero_labels)[j]] = 0;
    }
  }

  RNG_END();

  if (weights)
    igraph_inclist_destroy(&il);
  else
    igraph_adjlist_destroy(&al);
  IGRAPH_FINALLY_CLEAN(1);

  igraph_vector_bool_destroy(&in_queue);
  igraph_dqueue_destroy(&queue);
  igraph_vector_destroy(&label_counters);
  igraph_vector_destroy(&dominant_labels);
  igraph_vector_destroy(&nonzero_labels);
  IGRAPH_FINALLY_CLEAN(5);

  return IGRAPH_SUCCESS;
}

/**
 * \ingroup communities
 * \function igraph_community_label_propagation
 * \brief Community detection based on label propagation.
 *
 * This function implements the label propagation-based community detection
 * algorithm described by Raghavan, Albert and Kumara. This version extends
 * the original method by the ability to take edge weights into consideration
 * and also by allowing some labels to be fixed.
 *
 * </para><para>
 * Weights are taken into account as follows: when the new label of node
 * \c i is determined, the algorithm iterates over all edges incident on
 * node \c i and calculate the total weight of edges leading to other
 * nodes with label 0, 1, 2, ..., \c k - 1 (where \c k is the number of possible
 * labels). The new label of node \c i will then be the label whose edges
 * (among the ones incident on node \c i) have the highest total weight.
 *
 * </para><para>
 * Reference:
 *
 * </para><para>
 * Raghavan, U.N. and Albert, R. and Kumara, S.:
 * Near linear time algorithm to detect community structures in large-scale networks.
 * Phys Rev E 76, 036106. (2007).
 * https://doi.org/10.1103/PhysRevE.76.036106
 *
 * \param graph The input graph, should be undirected to make sense.
 * \param membership The membership vector, the result is returned here.
 *    For each vertex it gives the ID of its community (label).
 * \param weights The weight vector, it should contain a positive
 *    weight for all the edges.
 * \param initial The initial state. If \c NULL, every vertex will have
 *   a different label at the beginning. Otherwise it must be a vector
 *   with an entry for each vertex. Non-negative values denote different
 *   labels, negative entries denote vertices without labels. Unlabeled
 *   vertices which are not reachable from any labeled ones will remain
 *   unlabeled at the end of the label propagation process, and will be
 *   labeled in an additional step to avoid returning negative values in
 *   \p membership. In undirected graphs, this happens when entire connected
 *   components are unlabeled. Then, each unlabeled component will receive
 *   its own separate label. In directed graphs, the outcome of the
 *   additional labeling should be considered undefined and may change
 *   in the future; please do not rely on it.
 * \param fixed Boolean vector denoting which labels are fixed. Of course
 *   this makes sense only if you provided an initial state, otherwise
 *   this element will be ignored. Also note that vertices without labels
 *   cannot be fixed. If they are, this vector will be modified to
 *   make it consistent with \p initial.
 * \param modularity If not a null pointer, then it must be a pointer
 *   to a real number. The modularity score of the detected community
 *   structure is stored here.
 * \param lpa_variant Which variant of label propagation algorithm to run.
 *   One of
 *   \enumval IGRAPH_LPA_DOMINANCE Check for dominance of all nodes after
 *                                 each iteration
 *   \enumval IGRAPH_LPA_RETENTION Keep current label if among dominant labels,
 *                                 only check if labels changed
 *   \enumval IGRAPH_LPA_FAST Sample from dominant labels, only check neighbors
 *
 * \return Error code.
 *
 * Time complexity: O(m+n)
 *
 * \example examples/simple/igraph_community_label_propagation.c
 */
int igraph_community_label_propagation(const igraph_t *graph,
                                       igraph_vector_t *membership,
                                       const igraph_vector_t *weights,
                                       const igraph_vector_t *initial,
                                       const igraph_vector_bool_t *fixed,
                                       igraph_real_t *modularity,
                                       igraph_lpa_variant_t lpa_variant) {
    long int no_of_nodes = igraph_vcount(graph);
    long int no_of_edges = igraph_ecount(graph);
    long int no_of_not_fixed_nodes = no_of_nodes;
    long int i, j, k;
    igraph_bool_t unlabelled_left;
    igraph_vector_t label_counters, node_order;

    /* We make a copy of 'fixed' as a pointer into 'fixed_copy' after casting
     * away the constness, and promise ourselves that we will make a proper
     * copy of 'fixed' into 'fixed_copy' as soon as we start mutating it */
    igraph_vector_bool_t* fixed_copy = (igraph_vector_bool_t*) fixed;

    /* Unlabelled nodes are represented with -1. */
#define IS_UNLABELLED(x) (VECTOR(*membership)[x] < 0)

    /* Do some initial checks */
    if (fixed && igraph_vector_bool_size(fixed) != no_of_nodes) {
        IGRAPH_ERROR("Fixed labeling vector length must agree with number of nodes.", IGRAPH_EINVAL);
    }
    if (weights) {
        if (igraph_vector_size(weights) != no_of_edges) {
            IGRAPH_ERROR("Length of weight vector must agree with number of edges.", IGRAPH_EINVAL);
        }
        if (no_of_edges > 0) {
            igraph_real_t minweight = igraph_vector_min(weights);
            if (minweight < 0) {
                IGRAPH_ERROR("Weights must not be negative.", IGRAPH_EINVAL);
            }
            if (igraph_is_nan(minweight)) {
                IGRAPH_ERROR("Weights must not be NaN.", IGRAPH_EINVAL);
            }
        }
    }
    if (fixed && !initial) {
        IGRAPH_WARNING("Ignoring fixed vertices as no initial labeling given.");
    }

    IGRAPH_CHECK(igraph_vector_resize(membership, no_of_nodes));

    if (initial) {
        if (igraph_vector_size(initial) != no_of_nodes) {
            IGRAPH_ERROR("Initial labeling vector length must agree with number of nodes.", IGRAPH_EINVAL);
        }
        /* Check if the labels used are valid, initialize membership vector */
        for (i = 0; i < no_of_nodes; i++) {
            if (VECTOR(*initial)[i] < 0) {
                VECTOR(*membership)[i] = -1;
            } else {
                VECTOR(*membership)[i] = floor(VECTOR(*initial)[i]);
            }
        }
        if (fixed) {
            for (i = 0; i < no_of_nodes; i++) {
                if (VECTOR(*fixed)[i]) {
                    if (IS_UNLABELLED(i)) {
                        IGRAPH_WARNING("Fixed nodes cannot be unlabeled, ignoring them.");

                        /* We cannot modify 'fixed' because it is const, so we make a copy and
                         * modify 'fixed_copy' instead */
                        if (fixed_copy == fixed) {
                            fixed_copy = igraph_Calloc(1, igraph_vector_bool_t);
                            if (fixed_copy == 0) {
                                IGRAPH_ERROR("Failed to copy 'fixed' vector.", IGRAPH_ENOMEM);
                            }

                            IGRAPH_FINALLY(igraph_free, fixed_copy);
                            IGRAPH_CHECK(igraph_vector_bool_copy(fixed_copy, fixed));
                            IGRAPH_FINALLY(igraph_vector_bool_destroy, fixed_copy);
                        }

                        VECTOR(*fixed_copy)[i] = 0;
                    } else {
                        no_of_not_fixed_nodes--;
                    }
                }
            }
        }

        i = (long int) igraph_vector_max(membership);
        if (i > no_of_nodes) {
            IGRAPH_ERROR("Elements of the initial labeling vector must be between 0 and |V|-1.", IGRAPH_EINVAL);
        }
    } else {
        for (i = 0; i < no_of_nodes; i++) {
            VECTOR(*membership)[i] = i;
        }
    }

    /* From this point onwards we use 'fixed_copy' instead of 'fixed' */
    IGRAPH_VECTOR_INIT_FINALLY(&label_counters, no_of_nodes);

    switch(lpa_variant)
    {
       case IGRAPH_LPA_FAST:
        IGRAPH_CHECK(igraph_i_community_fast_label_propagation(graph, membership, weights, fixed_copy));
        break;

      case IGRAPH_LPA_RETENTION:
        IGRAPH_CHECK(igraph_i_community_label_propagation(graph, membership, weights, fixed_copy, /* retention */ 1 ));
        break;

      case IGRAPH_CK_LPA: 
        IGRAPH_CHECK(igraph_i_community_ck_label_propagation(graph, membership, weights, fixed_copy, /* retention */ 1 ));
        break; 
      
      case IGRAPH_DPC_LPA: 
        IGRAPH_CHECK(igraph_i_community_dpc_label_propagation(graph, membership, weights, fixed_copy, /* retention */ 1 ));
        break; 

      case IGRAPH_LPA_DOMINANCE:
      default:
        IGRAPH_CHECK(igraph_i_community_label_propagation(graph, membership, weights, fixed_copy, /* retention */ 0));
    }


    /* Permute labels in increasing order */
    igraph_vector_fill(&label_counters, -1);
    j = 0;
    unlabelled_left = 0;
    for (i = 0; i < no_of_nodes; i++) {
        k = (long)VECTOR(*membership)[i];
        if (k >= 0) {
            if (VECTOR(label_counters)[k] == -1) {
                /* We have seen this label for the first time */
                VECTOR(label_counters)[k] = j;
                k = j;
                j++;
            } else {
                k = (long int) VECTOR(label_counters)[k];
            }
        } else {
            /* This is an unlabeled vertex */
            unlabelled_left = 1;
        }
        VECTOR(*membership)[i] = k;
    }

    /* If any nodes are left unlabelled, we assign the remaining labels to them,
     * as well as to all unlabelled nodes reachable from them.
     *
     * Note that only those nodes could remain unlabelled which were unreachable
     * from any labelled ones. Thus, in the undirected case, fully unlabelled
     * connected components remain unlabelled. Here we label each such component
     * with the same label.
     */
    if (unlabelled_left) {
        igraph_dqueue_t q;
        igraph_vector_t neis;

        /* Initialize node ordering vector with only the not fixed nodes */
        if (fixed_copy) {
            IGRAPH_VECTOR_INIT_FINALLY(&node_order, no_of_not_fixed_nodes);
            for (i = 0, j = 0; i < no_of_nodes; i++) {
                if (!VECTOR(*fixed_copy)[i]) {
                    VECTOR(node_order)[j] = i;
                    j++;
                }
            }
        } else {
            IGRAPH_CHECK(igraph_vector_init_seq(&node_order, 0, no_of_nodes - 1));
            IGRAPH_FINALLY(igraph_vector_destroy, &node_order);
        }

        /* In the directed case, the outcome depends on the node ordering, thus we
         * shuffle nodes one more time. */
        IGRAPH_CHECK(igraph_vector_shuffle(&node_order));

        IGRAPH_VECTOR_INIT_FINALLY(&neis, 0);

        IGRAPH_CHECK(igraph_dqueue_init(&q, 0));
        IGRAPH_FINALLY(igraph_dqueue_destroy, &q);

        for (i=0; i < no_of_nodes; ++i) {
            long int v = VECTOR(node_order)[i];

            /* Is this node unlabelled? */
            if (IS_UNLABELLED(v)) {
                /* If yes, we label it, and do a BFS to apply the same label
                 * to all other unlabelled nodes reachable from it */
                igraph_dqueue_push(&q, v);
                VECTOR(*membership)[v] = j;
                while (!igraph_dqueue_empty(&q)) {
                    long int ni, num_neis;
                    long int actnode = igraph_dqueue_pop(&q);

                    IGRAPH_CHECK(igraph_neighbors(graph, &neis, actnode, IGRAPH_OUT));
                    num_neis = igraph_vector_size(&neis);

                    for (ni = 0; ni < num_neis; ++ni) {
                        long int neighbor = VECTOR(neis)[ni];
                        if (IS_UNLABELLED(neighbor)) {
                            VECTOR(*membership)[neighbor] = j;
                            IGRAPH_CHECK(igraph_dqueue_push(&q, neighbor));
                        }
                    }
                }
                j++;
            }
        }

        igraph_vector_destroy(&neis);
        igraph_dqueue_destroy(&q);
        igraph_vector_destroy(&node_order);
        IGRAPH_FINALLY_CLEAN(3);
    }

    if (modularity) {
      IGRAPH_CHECK(igraph_modularity(graph, membership, weights,
                                     /* resolution */ 1,
                                     /* directed */ 1, modularity));
    }

    igraph_vector_destroy(&label_counters);
    IGRAPH_FINALLY_CLEAN(1);
    if (fixed != fixed_copy) {
        igraph_vector_bool_destroy(fixed_copy);
        igraph_Free(fixed_copy);
        IGRAPH_FINALLY_CLEAN(2);
    }

    return IGRAPH_SUCCESS;
}
