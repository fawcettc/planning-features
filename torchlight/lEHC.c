

/*********************************************************************
 * (C) Copyright 2010 INRIA, France
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 * 
 *********************************************************************/

/*
 * THIS SOURCE CODE IS SUPPLIED  ``AS IS'' WITHOUT WARRANTY OF ANY KIND, 
 * AND ITS AUTHOR AND THE JOURNAL OF ARTIFICIAL INTELLIGENCE RESEARCH 
 * (JAIR) AND JAIR'S PUBLISHERS AND DISTRIBUTORS, DISCLAIM ANY AND ALL 
 * WARRANTIES, INCLUDING BUT NOT LIMITED TO ANY IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, AND
 * ANY WARRANTIES OR NON INFRINGEMENT.  THE USER ASSUMES ALL LIABILITY AND
 * RESPONSIBILITY FOR USE OF THIS SOURCE CODE, AND NEITHER THE AUTHOR NOR
 * JAIR, NOR JAIR'S PUBLISHERS AND DISTRIBUTORS, WILL BE LIABLE FOR 
 * DAMAGES OF ANY KIND RESULTING FROM ITS USE.  Without limiting the 
 * generality of the foregoing, neither the author, nor JAIR, nor JAIR's
 * publishers and distributors, warrant that the Source Code will be 
 * error-free, will operate without interruption, or will meet the needs 
 * of the user.
 */



/*********************************************************************
 * File: lEHC.c
 *
 * Description: local search state analysis by monotone-one-step-EHC
 *
 * Author: Joerg Hoffmann
 *
 *********************************************************************/ 






#include "torchlight.h"
#include "output.h"
#include "lEHC.h"
























/**********************
 * monotone-one-step-EHC
 **********************/























/* Let $(\vars,\ini,\goal,\ops)$ be a planning task, and let $s \in
 * \statespace$ be a state with $0 < \hplus(s) < \infty$. Say that
 * $\var_0 \in \vars$ so that, for every $\op_0 = \rop(s(\var_0),c)$
 * in $\dtg_{\var_0}$ where $(s(\var_0),c)$ is not irrelevant,
 * $\ldg_{\op_0} = (V,A)$ is a local dependency graph for $s$ where:
 * $(s(\var_0),c)$ either has irrelevant side effect deletes, or has
 * irrelevant side effects and recoverable side effect deletes; and
 * the $\dtg_\var$ transitions of every $\var \in V \setminus
 * \{\var_0\}$ either are irrelevant, or are invertible or potentially
 * induced and have no side effects, or have an irrelevant own-delete
 * and irrelevant side effect deletes. 
 *
 * Then $s$ is not a local minimum. Then $\ed(s) \leq \max_{\op_0}
 * \Dcost(\ldg_{\op_0})$, and $\ed(s) \leq \max_{\op_0}
 * \Dcost(\ldg_{\op_0}) - 1$ if every $(s(\var_0),c)$ has irrelevant
 * side effect deletes.
 *
 * This function minimizes the ed bound over all var0s for which the
 * claim could be applied.
 */

void analyze_local_monotoneEHC( State *s )

{

  /* set defaults for return values
   */
  gsuccess = FALSE;
  ged_bound = -1;
  gdead_end = FALSE;

  gdoing_EHCanalyze = TRUE;
  gsuccess = do_enforced_hill_climbing( s, &ggoal_state );
  gdoing_EHCanalyze = FALSE;

}


















/**********************
 * Control for analysis of samples
 **********************/




















void analyze_samples_local_monotoneEHC( void )

{

  int i;
  int num_success = 0;
  int min_ed_bound = -1;
  float mean_ed_bound = 0;
  int max_ed_bound = -1;
  int num_dead_end = 0;

  for ( i = 0; i < gcmd_line.num_samples; i++ ) {

    analyze_local_monotoneEHC( &(gsample_states[i]) );

    if ( gsuccess ) {
      num_success++;

      if ( min_ed_bound == -1 || ged_bound < min_ed_bound ) {
	min_ed_bound = ged_bound;
      }

      if ( max_ed_bound == -1 || ged_bound > max_ed_bound ) {
	max_ed_bound = ged_bound;
      }

      mean_ed_bound += ged_bound;
      
    }

    if ( gdead_end ) {
      num_dead_end++;
    }

  }

  gsuccess_percentage = ((float) num_success) / ((float) gcmd_line.num_samples) * 100.0;
  gmin_ed_bound = min_ed_bound;
  gmax_ed_bound = max_ed_bound;
  gmean_ed_bound = mean_ed_bound / ((float) gcmd_line.num_samples);
  gdead_end_percentage = ((float) num_dead_end) / ((float) gcmd_line.num_samples) * 100.0;

}
