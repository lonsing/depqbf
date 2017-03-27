/*
 This file is part of DepQBF4J.

 DepQBF4J, a tool that enables Java applications to use DepQBF as a library.

 Copyright 2014, 2015 Martin Kronegger and Andreas Pfandler
 Vienna University of Technology, Vienna, Austria.

 DepQBF4J is free software: you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License, or (at
 your option) any later version.

 DepQBF4J is distributed in the hope that it will be useful, but
 WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with DepQBF4J. If not, see <http://www.gnu.org/licenses/>.
*/

#include "../../qdpll.h"
#include "depqbf4j_DepQBF4J.h"
#include <stdlib.h>

#define FORCE_FLUSH 1

QDPLL * solver;

JNIEXPORT void JNICALL Java_depqbf4j_DepQBF4J_create (JNIEnv * env, jclass cls) {
	solver = qdpll_create();
}

JNIEXPORT void JNICALL Java_depqbf4j_DepQBF4J_delete (JNIEnv * env, jclass cls) {
	qdpll_delete(solver);
	solver = 0;
}

JNIEXPORT jstring JNICALL Java_depqbf4j_DepQBF4J_configure (JNIEnv * env, jclass cls, jstring conf_str) {
	const char * str = (*env)->GetStringUTFChars(env,conf_str,0);
	char * result = qdpll_configure(solver,(char*)str);
	(*env)->ReleaseStringUTFChars(env, conf_str, str);
	return (*env)->NewStringUTF(env, result);
}

JNIEXPORT void JNICALL Java_depqbf4j_DepQBF4J_adjustVars (JNIEnv * env, jclass cls, jint varID) {
	qdpll_adjust_vars(solver, varID);
}

JNIEXPORT jint JNICALL Java_depqbf4j_DepQBF4J_getMaxScopeNesting (JNIEnv * env, jclass cls) {
	return qdpll_get_max_scope_nesting (solver);
}

JNIEXPORT jint JNICALL Java_depqbf4j_DepQBF4J_pop (JNIEnv * env, jclass cls) {
	return qdpll_pop(solver);
}

JNIEXPORT void JNICALL Java_depqbf4j_DepQBF4J_gc (JNIEnv * env, jclass cls) {
	qdpll_gc(solver);
}

JNIEXPORT jint JNICALL Java_depqbf4j_DepQBF4J_push (JNIEnv * env, jclass cls) {
	return qdpll_push(solver);
}

JNIEXPORT jint JNICALL Java_depqbf4j_DepQBF4J_newScope (JNIEnv * env, jclass cls, jbyte qType) {
	return qdpll_new_scope(solver,qType);
}

JNIEXPORT jint JNICALL Java_depqbf4j_DepQBF4J_newScopeAtNesting (JNIEnv * env, jclass cls, jbyte qType, jint nesting) {
	return qdpll_new_scope_at_nesting(solver,qType,nesting);
}

JNIEXPORT void JNICALL Java_depqbf4j_DepQBF4J_addVarToScope (JNIEnv * env, jclass cls, jint id, jint nesting) {
	qdpll_add_var_to_scope (solver,id,nesting);
}

JNIEXPORT jboolean JNICALL Java_depqbf4j_DepQBF4J_hasVarActiveOccs (JNIEnv * env, jclass cls, jint varID) {
	return qdpll_has_var_active_occs (solver, varID);
}

JNIEXPORT void JNICALL Java_depqbf4j_DepQBF4J_add (JNIEnv * env, jclass cls, jint litID) {
	qdpll_add(solver, litID);
}


JNIEXPORT jbyte JNICALL Java_depqbf4j_DepQBF4J_sat (JNIEnv * env, jclass cls) {
	return qdpll_sat(solver);
}

JNIEXPORT jbyte JNICALL Java_depqbf4j_DepQBF4J_getValue (JNIEnv * env, jclass cls, jint varID) {
	return qdpll_get_value(solver,varID);
}

JNIEXPORT void JNICALL Java_depqbf4j_DepQBF4J_printToStdOut (JNIEnv * env, jclass cls) {
	qdpll_print(solver,stdout);
	#if FORCE_FLUSH
		fflush(stdout);
	#endif
}

JNIEXPORT void JNICALL Java_depqbf4j_DepQBF4J_printToFile (JNIEnv * env, jclass cls, jstring name) {
	const char *str;
	str = (*env)->GetStringUTFChars(env, name, NULL);

	FILE *f = fopen(str, "w");
	qdpll_print(solver,f);
	fclose(f);

	(*env)->ReleaseStringUTFChars(env, name, str);
}

JNIEXPORT void JNICALL Java_depqbf4j_DepQBF4J_printQdimacsOutput (JNIEnv * env, jclass cls) {
	qdpll_print_qdimacs_output(solver);
}

JNIEXPORT void JNICALL Java_depqbf4j_DepQBF4J_initDeps (JNIEnv * env, jclass cls) {
	qdpll_init_deps(solver);
}

JNIEXPORT void JNICALL Java_depqbf4j_DepQBF4J_resetDeps (JNIEnv * env, jclass cls) {
	qdpll_reset_deps (solver);
}

JNIEXPORT jboolean JNICALL Java_depqbf4j_DepQBF4J_varDepends (JNIEnv * env, jclass cls, jint varID1, jint varID2) {
	return qdpll_var_depends(solver, varID1, varID2);
}

JNIEXPORT void JNICALL Java_depqbf4j_DepQBF4J_printDeps (JNIEnv * env, jclass cls, jint varID) {
	qdpll_print_deps(solver,varID);
}

JNIEXPORT jint JNICALL Java_depqbf4j_DepQBF4J_getMaxDeclaredVarId (JNIEnv * env, jclass cls) {
	return qdpll_get_max_declared_var_id (solver);
}

JNIEXPORT jboolean JNICALL Java_depqbf4j_DepQBF4J_isVarDeclared (JNIEnv * env, jclass cls, jint varID) {
	return qdpll_is_var_declared (solver, varID);
}

JNIEXPORT jint JNICALL Java_depqbf4j_DepQBF4J_getNestingOfVar (JNIEnv * env, jclass cls, jint varID) {
	return qdpll_get_nesting_of_var(solver, varID);
}

JNIEXPORT jbyte JNICALL Java_depqbf4j_DepQBF4J_getScopeType (JNIEnv * env, jclass cls, jint nesting) {
	return qdpll_get_scope_type (solver, nesting);
}

JNIEXPORT void JNICALL Java_depqbf4j_DepQBF4J_dumpDepGraph (JNIEnv * env, jclass cls) {
	qdpll_dump_dep_graph(solver);
}

JNIEXPORT void JNICALL Java_depqbf4j_DepQBF4J_printStats (JNIEnv * env, jclass cls) {
	qdpll_print_stats(solver);
}

JNIEXPORT void JNICALL Java_depqbf4j_DepQBF4J_reset (JNIEnv * env, jclass cls) {
	qdpll_reset(solver);
}

JNIEXPORT void JNICALL Java_depqbf4j_DepQBF4J_resetStats (JNIEnv * evn, jclass cls) {
	qdpll_reset_stats(solver);
}

JNIEXPORT void JNICALL Java_depqbf4j_DepQBF4J_resetLearnedConstraints (JNIEnv *env, jclass cls) {
	qdpll_reset_learned_constraints(solver);
}

JNIEXPORT void JNICALL Java_depqbf4j_DepQBF4J_assume (JNIEnv * env, jclass cls, jint litID) {
	qdpll_assume (solver, litID);
}

JNIEXPORT jintArray JNICALL Java_depqbf4j_DepQBF4J_getAssumptionCandidates (JNIEnv * env, jclass cls) {
	jintArray result;
	LitID * ac = qdpll_get_assumption_candidates(solver);
	int numElem = sizeof(ac) / sizeof(LitID);
	
	result = (*env)->NewIntArray(env, numElem);
	if (result == NULL) {
		return NULL; /* out of memory */
	}
	
	(*env)->SetIntArrayRegion(env,result,0,numElem,ac); 
	
	free(ac);
	return result;
}

JNIEXPORT jintArray JNICALL Java_depqbf4j_DepQBF4J_getRelevantAssumptions (JNIEnv * env, jclass cls) {
	jintArray result;
	LitID * ra = qdpll_get_relevant_assumptions(solver);
	int numElem = sizeof(ra) / sizeof(LitID);
	
	result = (*env)->NewIntArray(env, numElem);
	if (result == NULL) {
		return NULL; /* out of memory */
	}
	
	(*env)->SetIntArrayRegion(env,result,0,numElem,ra); 
	
	free(ra);
	return result;
}

/* ------------ START: API functions for clause groups ------------ */

JNIEXPORT jint JNICALL Java_depqbf4j_DepQBF4J_newClauseGroup (JNIEnv * env, jclass cls) {
	return qdpll_new_clause_group (solver);
}

JNIEXPORT void JNICALL Java_depqbf4j_DepQBF4J_deleteClauseGroup (JNIEnv * env, jclass cls, jint cgid) {
	qdpll_delete_clause_group (solver, cgid);
}

JNIEXPORT void JNICALL Java_depqbf4j_DepQBF4J_openClauseGroup (JNIEnv * env, jclass cls, jint cgid) {
	qdpll_open_clause_group (solver, cgid);
}

JNIEXPORT jint JNICALL Java_depqbf4j_DepQBF4J_getOpenClauseGroup (JNIEnv * env, jclass cls) {
	return qdpll_get_open_clause_group (solver);
}

JNIEXPORT jboolean JNICALL Java_depqbf4j_DepQBF4J_existsClauseGroup (JNIEnv * env, jclass cls, jint cgid) {
	return qdpll_exists_clause_group (solver, cgid);
}

JNIEXPORT void JNICALL Java_depqbf4j_DepQBF4J_closeClauseGroup (JNIEnv * env, jclass cls, jint cgid) {
	qdpll_close_clause_group (solver, cgid);
}

JNIEXPORT jintArray JNICALL Java_depqbf4j_DepQBF4J_getRelevantClauseGroups (JNIEnv * env, jclass cls) {
	jintArray result;
        ClauseGroupID * ra = qdpll_get_relevant_clause_groups(solver);
	int numElem = sizeof(ra) / sizeof(ClauseGroupID);
	
	result = (*env)->NewIntArray(env, numElem);
	if (result == NULL) {
		return NULL; /* out of memory */
	}
	
	(*env)->SetIntArrayRegion(env,result,0,numElem,(const jint *)ra); 
	
	free(ra);
	return result;
}

JNIEXPORT void JNICALL Java_depqbf4j_DepQBF4J_activateClauseGroup (JNIEnv * env, jclass cls, jint cgid) {
	qdpll_activate_clause_group (solver, cgid);
}

JNIEXPORT void JNICALL Java_depqbf4j_DepQBF4J_deactivateClauseGroup (JNIEnv * env, jclass cls, jint cgid) {
	qdpll_deactivate_clause_group (solver, cgid);
}

/* ------------ END: API functions for clause groups ------------ */
