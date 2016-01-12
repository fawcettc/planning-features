

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
 * File: gDGs-lDGs.h
 *
 * Description: extraction and analysis of global dependency graphs
 * and local dependency graphs
 *
 * Author: Joerg Hoffmann
 *
 *********************************************************************/ 






#ifndef _GDGS_LDGS_H
#define _GDGS_LDGS_H



void analyze_global( void );
Bool construct_gDG( int var0, DTGTransition *t0 );



void analyze_local_lDG( State *s );
Bool construct_lDG( int *s_on_var, int var0, DTGTransition *t0 );



void analyze_samples_local_lDG( void );



#endif /* _GDGS_LDGS_H */
