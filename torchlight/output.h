


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
 * File: output.h
 * Description: print headers
 *
 * Author: Joerg Hoffmann 1999
 *
 *********************************************************************/ 





#ifndef _OUTPUT_H
#define _OUTPUT_H



void print_FactList( FactList *list, char *sepf, char *sept );
void print_hidden_TokenList( TokenList *list, char *sep );
void print_indent( int indent );
void print_PlNode( PlNode *plnode, int indent );
void print_Wff( WffNode *n, int indent );
void print_plops( PlOperator *plop );
void print_Operator( Operator *o );
void print_NormOperator( NormOperator *o );
void print_MixedOperator( MixedOperator *o );
void print_PseudoAction( PseudoAction *o );
void print_Action( Action *a );
void print_type( int t );
void print_Fact( Fact *f ); 
void print_ft_name( int index );
void print_op_name( int index );
void print_Variable_Value( int var, int val, Bool verbose );
void print_Variable( int var );
void print_SG( void );
void print_DTG( int var );
void print_DTGTransition( DTGTransition *t, Bool verbose );



void print_plan( void );



#endif /* _OUTPUT_H */
