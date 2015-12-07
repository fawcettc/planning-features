


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
 * File: SG-DTG.h
 * Description: creation of variables, support graph, DTGs
 *
 * Author: Joerg Hoffmann
 *
 *********************************************************************/ 






#ifndef _SG_DTG_H
#define _SG_DTG_H



void create_and_parse_variables( void );
void get_name( char *tmp, int pos, char *name );
int find_ft_from_parsedvarval( char *predicate, int num_args, char **args );



void create_ft_op_indices( void );



void create_SG_DTG( void );
void insert_DTG_transition( int var, int start, int end, int op, int eff );



void determine_SG_DTG_static_properties( void );
void determine_SG_acyclic( void );
void determine_DTGt_invertible( void );
void determine_DTGt_no_side_effects( void );
void determine_DTGt_irrelevant( void );
void determine_DTGt_irrelevant_own_delete( void );
void determine_DTGt_irrelevant_side_effect_deletes( void );
void determine_DTGt_replacable_side_effect_deletes( void );
Bool is_replacable_precond( int ft, int rop );
void determine_DTGt_irrelevant_side_effects( void );
void determine_DTGt_recoverable_side_effect_deletes( void );
Bool recoverable_side_effect_deletes_testPSI( DTGTransition *t, 
					      int current_ctxvar_index );
Bool is_potential_recoverer( DTGTransition *t, int op );
void determine_DTG_overall( void );
void determine_DTG_diameters( void );
void determine_DTG_maxdiameters( void );
int DTG_bfs_maxdiameter( DTG *dtg, DTGNode *node );



Bool SG_INsubgraph_acyclic( void );
int DTG_bfs_diameter( DTG *dtg, DTGNode *node );
Bool SG_fullDTGs_INsubgraph_nonleafs_qualifies( int var0, DTGTransition *t0 );
int SG_fullDTGs_INsubgraph_Dcost( int var0 );
void SG_fullDTGs_INsubgraph_Dcost_recursive( SGNode *node0, SGNode *current_node );
Bool SG_DTGs_oDGplus_INsubgraph_nonleafs_qualifies( int var0 );
int SG_DTGs_oDGplus_INsubgraph_dcost( int var0 );
void SG_DTGs_oDGplus_INsubgraph_dcost_recursive( SGNode *node0, SGNode *current_node );



Bool are_exchanged_predicates( int p1, int p2 );



#endif /* _SG_DTG_H */
