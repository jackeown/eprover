/*-----------------------------------------------------------------------

  File  : cco_proofproc.c

  Author: Stephan Schulz

  Contents

  Functions realizing the proof procedure.

  Copyright 1998--2018 by the author.
  This code is released under the GNU General Public Licence and
  the GNU Lesser General Public License.
  See the file COPYING in the main E directory for details..
  Run "eprover -h" for contact information.

Changes

<1> Mon Jun  8 11:47:44 MET DST 1998
    New

-----------------------------------------------------------------------*/
#include "mcts.h"

#include "cco_proofproc.h"
#include <picosat.h>
#include <cco_ho_inferences.h>
#include <cte_ho_csu.h>

#include <NNetInterface.hpp>



/*---------------------------------------------------------------------*/
/*                        Global Variables                             */
/*---------------------------------------------------------------------*/

PERF_CTR_DEFINE(ParamodTimer);
PERF_CTR_DEFINE(BWRWTimer);


MCTSNode_p MCTSRoot;
MCTSNode_p MCTSChosen;
MCTSNode_p MCTSSimulated;
Model criticModel;

int StatePipe;
int ActionPipe;
int RewardPipe;
RLProofStateCell rlstate;
ClauseSet_p rl_weight_tracking;
int sync_num;

long long statePipeTimeSpent = 0;
long long actionPipeTimeSpent = 0;
long long rewardPipeTimeSpent = 0;
long long statePrepTimeSpent = 0;

bool smartPhaseKilled = false;



/*---------------------------------------------------------------------*/
/*                      Forward Declarations                           */
/*---------------------------------------------------------------------*/


/*---------------------------------------------------------------------*/
/*                         Internal Functions                          */
/*---------------------------------------------------------------------*/

/*-----------------------------------------------------------------------
//
// Function: document_processing()
//
//   Document processing of the new given clause (depending on the
//   output level).
//
// Global Variables: OutputLevel, GlobalOut (read only)
//
// Side Effects    : Output
//
/----------------------------------------------------------------------*/

void document_processing(Clause_p clause)
{
   if(OutputLevel)
   {
      if(OutputLevel == 1)
      {
         putc('\n', GlobalOut);
         putc('#', GlobalOut);
         ClausePrint(GlobalOut, clause, true);
         //DerivationDebugPrint(GlobalOut, clause->derivation);
         putc('\n', GlobalOut);
      }
      DocClauseQuoteDefault(6, clause, "new_given");
   }
}

/*-----------------------------------------------------------------------
//
// Function: check_ac_status()
//
//   Check if the AC theory has been extended by the currently
//   processed clause, and act accordingly.
//
// Global Variables: -
//
// Side Effects    : Changes AC status in signature
//
/----------------------------------------------------------------------*/

static void check_ac_status(ProofState_p state, ProofControl_p
                            control, Clause_p clause)
{
   if(control->heuristic_parms.ac_handling!=NoACHandling)
   {
      bool res;
      res = ClauseScanAC(state->signature, clause);
      if(res && !control->ac_handling_active)
      {
         control->ac_handling_active = true;
         if(OutputLevel)
         {
            SigPrintACStatus(GlobalOut, state->signature);
            fprintf(GlobalOut, "# AC handling enabled dynamically\n");
         }
      }
   }
}


/*-----------------------------------------------------------------------
//
// Function: remove_subsumed()
//
//   Remove all clauses subsumed by subsumer from set, kill their
//   children. Return number of removed clauses.
//
// Global Variables: -
//
// Side Effects    : Changes set, memory operations.
//
/----------------------------------------------------------------------*/

static long remove_subsumed(GlobalIndices_p indices,
                            FVPackedClause_p subsumer,
                            ClauseSet_p set,
                            ClauseSet_p archive,
                            bool lambda_demod)
{
   Clause_p handle;
   long     res;
   PStack_p stack = PStackAlloc();

   res = ClauseSetFindFVSubsumedClauses(set, subsumer, stack);

   while(!PStackEmpty(stack))
   {
      handle = PStackPopP(stack);
      //printf("# XXX Removing (remove_subumed()) %p from %p = %p\n", handle, set, handle->set);
      if(ClauseQueryProp(handle, CPWatchOnly))
      {
         DocClauseQuote(GlobalOut, OutputLevel, 6, handle,
                        "extract_wl_subsumed", subsumer->clause);

      }
      else
      {
         DocClauseQuote(GlobalOut, OutputLevel, 6, handle,
                        "subsumed", subsumer->clause);
      }


      if (
          set == rlstate.state->processed_neg_units || 
          set == rlstate.state->processed_non_units ||
          set == rlstate.state->processed_pos_eqns  ||
          set == rlstate.state->processed_pos_rules
      ){
            rlstate.processedWeightSum -= (long long) handle->weight;
      }

      GlobalIndicesDeleteClause(indices, handle, lambda_demod);
      ClauseSetExtractEntry(handle);
      ClauseSetProp(handle, CPIsDead);
      ClauseSetInsert(archive, handle);
   }
   PStackFree(stack);
   return res;
}


/*-----------------------------------------------------------------------
//
// Function: eliminate_backward_rewritten_clauses()
//
//   Remove all processed clauses rewritable with clause and put
//   them into state->tmp_store.
//
// Global Variables: -
//
// Side Effects    : Changes clause sets
//
/----------------------------------------------------------------------*/

static bool
eliminate_backward_rewritten_clauses(ProofState_p
                                     state, ProofControl_p control,
                                     Clause_p clause, SysDate *date)
{
   long old_lit_count = state->tmp_store->literals,
      old_clause_count= state->tmp_store->members;
   bool min_rw = false;

   assert(rl_weight_tracking->members == 0);

   
   PERF_CTR_ENTRY(BWRWTimer);
   if(ClauseIsDemodulator(clause))
   {
      SysDateInc(date);
      if(state->gindices.bw_rw_index)
      {
         min_rw = RemoveRewritableClausesIndexed(control->ocb,
                                                 rl_weight_tracking,
                                                 state->archive,
                                                 clause, *date, &(state->gindices),
                                                 control->heuristic_parms.lambda_demod);

      }
      else
      {
         min_rw = RemoveRewritableClauses(control->ocb,
                                          state->processed_pos_rules,
                                          rl_weight_tracking,
                                          state->archive,
                                          clause, *date, &(state->gindices),
                                          control->heuristic_parms.lambda_demod)
            ||min_rw;
         min_rw = RemoveRewritableClauses(control->ocb,
                                          state->processed_pos_eqns,
                                          rl_weight_tracking,
                                          state->archive,
                                          clause, *date, &(state->gindices),
                                          control->heuristic_parms.lambda_demod)
            ||min_rw;
         min_rw = RemoveRewritableClauses(control->ocb,
                                          state->processed_neg_units,
                                          rl_weight_tracking,
                                          state->archive,
                                          clause, *date, &(state->gindices),
                                          control->heuristic_parms.lambda_demod)
            ||min_rw;
         min_rw = RemoveRewritableClauses(control->ocb,
                                          state->processed_non_units,
                                          rl_weight_tracking,
                                          state->archive,
                                          clause, *date, &(state->gindices),
                                          control->heuristic_parms.lambda_demod)
            ||min_rw;
      }

      Clause_p handle=rl_weight_tracking->anchor->succ;
      while(rl_weight_tracking->members > 0){
         Clause_p next = handle->succ;
         rlstate.processedWeightSum -= (long long) ClauseStandardWeight(handle);
         ClauseSetMoveClause(state->tmp_store, handle);
         handle = next;
      }


      state->backward_rewritten_lit_count+=
         (state->tmp_store->literals-old_lit_count);
      state->backward_rewritten_count+=
         (state->tmp_store->members-old_clause_count);

      if(control->heuristic_parms.detsort_bw_rw)
      {
         ClauseSetSort(state->tmp_store, ClauseCmpByStructWeight);
      }
   }
   PERF_CTR_EXIT(BWRWTimer);
   /*printf("# Removed %ld clauses\n",
     (state->tmp_store->members-old_clause_count)); */
   return min_rw;
}


/*-----------------------------------------------------------------------
//
// Function: eliminate_backward_subsumed_clauses()
//
//   Eliminate subsumed processed clauses, return number of clauses
//   deleted.
//
// Global Variables: -
//
// Side Effects    : Changes clause sets.
//
/----------------------------------------------------------------------*/

static long eliminate_backward_subsumed_clauses(ProofState_p state,
                                                FVPackedClause_p pclause,
                                                bool lambda_demod)
{
   long res = 0;

   if(ClauseLiteralNumber(pclause->clause) == 1)
   {
      if(pclause->clause->pos_lit_no)
      {
         /* A unit rewrite rule that is a variant of an old rule is
            already subsumed by the older one.
            A unit rewrite rule can never subsume an unorientable
            equation (else it would be unorientable itself). */
         if(!ClauseIsRWRule(pclause->clause))
         {
            res += remove_subsumed(&(state->gindices), pclause,
                                   state->processed_pos_rules,
                                   state->archive, lambda_demod);
            res += remove_subsumed(&(state->gindices), pclause,
                                   state->processed_pos_eqns,
                                   state->archive, lambda_demod);
         }
         res += remove_subsumed(&(state->gindices), pclause,
                                state->processed_non_units,
                                state->archive, lambda_demod);
      }
      else
      {
         res += remove_subsumed(&(state->gindices), pclause,
                                state->processed_neg_units,
                                state->archive, lambda_demod);
         res += remove_subsumed(&(state->gindices), pclause,
                                state->processed_non_units,
                                state->archive, lambda_demod);
      }
   }
   else
   {
      res += remove_subsumed(&(state->gindices), pclause,
                             state->processed_non_units,
                             state->archive, lambda_demod);
   }
   state->backward_subsumed_count+=res;
   return res;
}



/*-----------------------------------------------------------------------
//
// Function: eliminate_unit_simplified_clauses()
//
//   Perform unit-back-simplification on the proof state.
//
// Global Variables: -
//
// Side Effects    : Potentially changes and moves clauses.
//
/----------------------------------------------------------------------*/

static void eliminate_unit_simplified_clauses(ProofState_p state,
                                              Clause_p clause,
                                              bool lambda_demod)
{

   if(ClauseIsRWRule(clause)||!ClauseIsUnit(clause))
   {
      return;
   }

   assert(rl_weight_tracking->members == 0);

   ClauseSetUnitSimplify(state->processed_non_units, clause,
                         rl_weight_tracking,
                         state->archive,
                         &(state->gindices),
                         lambda_demod);
   if(ClauseIsPositive(clause))
   {
      ClauseSetUnitSimplify(state->processed_neg_units, clause,
                            rl_weight_tracking,
                            state->archive,
                            &(state->gindices),
                           lambda_demod);
   }
   else
   {
      ClauseSetUnitSimplify(state->processed_pos_rules, clause,
                            rl_weight_tracking,
                            state->archive,
                            &(state->gindices),
                           lambda_demod);
      ClauseSetUnitSimplify(state->processed_pos_eqns, clause,
                            rl_weight_tracking,
                            state->archive,
                            &(state->gindices),
                           lambda_demod);
   }

   Clause_p handle=rl_weight_tracking->anchor->succ;
   while(rl_weight_tracking->members > 0){
      Clause_p next = handle->succ;
      rlstate.processedWeightSum -= (long long) ClauseStandardWeight(handle);
      ClauseSetMoveClause(state->tmp_store, handle);
      handle = next;
   }


}

/*-----------------------------------------------------------------------
//
// Function: eliminate_context_sr_clauses()
//
//   If required by control, remove all
//   backward-contextual-simplify-reflectable clauses.
//
// Global Variables: -
//
// Side Effects    : Moves clauses from state->processed_non_units
//                   to state->tmp_store
//
/----------------------------------------------------------------------*/

static long eliminate_context_sr_clauses(ProofState_p state,
                                         ProofControl_p control,
                                         Clause_p clause,
                                         bool lambda_demod)
{

   assert(rl_weight_tracking->members == 0);

   if(!control->heuristic_parms.backward_context_sr)
   {
      return 0;
   }
   long numRemoved = RemoveContextualSRClauses(state->processed_non_units,
                                    rl_weight_tracking,
                                    state->archive,
                                    clause,
                                    &(state->gindices),
                                    lambda_demod);

   Clause_p handle=rl_weight_tracking->anchor->succ;
   while(rl_weight_tracking->members > 0){
      Clause_p next = handle->succ;
      rlstate.processedWeightSum -= (long long) ClauseStandardWeight(handle);
      ClauseSetMoveClause(state->tmp_store, handle);
      handle = next;
   }

   return numRemoved;
}

/*-----------------------------------------------------------------------
//
// Function: check_watchlist()
//
//   Check if a clause subsumes one or more watchlist clauses, if yes,
//   set appropriate property in clause and remove subsumed clauses.
//
// Global Variables: -
//
// Side Effects    : As decribed.
//
/----------------------------------------------------------------------*/


void check_watchlist(GlobalIndices_p indices, ClauseSet_p watchlist,
                     Clause_p clause, ClauseSet_p archive,
                     bool static_watchlist, bool lambda_demod)
{
   FVPackedClause_p pclause;
   long removed;

   if(watchlist)
   {
      pclause = FVIndexPackClause(clause, watchlist->fvindex);
      // printf("# check_watchlist(%p)...\n", indices);
      ClauseSubsumeOrderSortLits(clause);
      // assert(ClauseIsSubsumeOrdered(clause));

      clause->weight = ClauseStandardWeight(clause);

      if(static_watchlist)
      {
         Clause_p subsumed;

         subsumed = ClauseSetFindFirstSubsumedClause(watchlist, clause);
         if(subsumed)
         {
            ClauseSetProp(clause, CPSubsumesWatch);
         }
      }
      else
      {
         if((removed = remove_subsumed(indices, pclause, watchlist, archive, lambda_demod)))
         {
            ClauseSetProp(clause, CPSubsumesWatch);
            if(OutputLevel == 1)
            {
               fprintf(GlobalOut,"# Watchlist reduced by %ld clause%s\n",
                       removed,removed==1?"":"s");
            }
            // ClausePrint(GlobalOut, clause, true); printf("\n");
            DocClauseQuote(GlobalOut, OutputLevel, 6, clause,
                           "extract_subsumed_watched", NULL);   }
      }
      FVUnpackClause(pclause);
      // printf("# ...check_watchlist()\n");
   }
}


/*-----------------------------------------------------------------------
//
// Function: simplify_watchlist()
//
//   Simplify all clauses in state->watchlist with processed positive
//   units from state. Assumes that all those clauses are in normal
//   form with respect to all clauses but clause!
//
// Global Variables: -
//
// Side Effects    : Changes watchlist, introduces new rewrite links
//                   into the term bank!
//
/----------------------------------------------------------------------*/

void simplify_watchlist(ProofState_p state, ProofControl_p control,
                        Clause_p clause)
{
   ClauseSet_p tmp_set;
   Clause_p handle;
   long     removed_lits;

   if(!ClauseIsDemodulator(clause))
   {
      return;
   }
   // printf("# simplify_watchlist()...\n");
   tmp_set = ClauseSetAlloc();

   if(state->wlindices.bw_rw_index)
   {
      // printf("# Simpclause: "); ClausePrint(stdout, clause, true); printf("\n");
      RemoveRewritableClausesIndexed(control->ocb,
                                     tmp_set, state->archive,
                                     clause, clause->date,
                                     &(state->wlindices),
                                     control->heuristic_parms.lambda_demod);
      // printf("# Simpclause done\n");
   }
   else
   {
      RemoveRewritableClauses(control->ocb, state->watchlist,
                              tmp_set, state->archive,
                              clause, clause->date,
                              &(state->wlindices),
                              control->heuristic_parms.lambda_demod);
   }
   while((handle = ClauseSetExtractFirst(tmp_set)))
   {
      // printf("# WL simplify: "); ClausePrint(stdout, handle, true);
      // printf("\n");
      ClauseComputeLINormalform(control->ocb,
                                state->terms,
                                handle,
                                state->demods,
                                control->heuristic_parms.forward_demod,
                                control->heuristic_parms.prefer_general,
                                control->heuristic_parms.lambda_demod);
      removed_lits = ClauseRemoveSuperfluousLiterals(handle);
      if(removed_lits)
      {
         DocClauseModificationDefault(handle, inf_minimize, NULL);
      }
      if(control->ac_handling_active)
      {
         ClauseRemoveACResolved(handle);
      }
      handle->weight = ClauseStandardWeight(handle);
      ClauseMarkMaximalTerms(control->ocb, handle);
      ClauseSetIndexedInsertClause(state->watchlist, handle);
      // printf("# WL Inserting: "); ClausePrint(stdout, handle, true); printf("\n");
      GlobalIndicesInsertClause(&(state->wlindices), handle, control->heuristic_parms.lambda_demod);
   }
   ClauseSetFree(tmp_set);
   // printf("# ...simplify_watchlist()\n");
}


/*-----------------------------------------------------------------------
//
// Function: generate_new_clauses()
//
//   Apply the generating inferences to the proof state, putting new
//   clauses into state->tmp_store.
//
// Global Variables: -
//
// Side Effects    : Changes proof state as described.
//
/----------------------------------------------------------------------*/

static void generate_new_clauses(ProofState_p state, ProofControl_p
                                 control, Clause_p clause, Clause_p tmp_copy)
{
   VarBankSetVCountsToUsed(state->terms->vars);
   ComputeHOInferences(state,control,tmp_copy,clause);
   if(control->heuristic_parms.enable_eq_factoring)
   {
      state->factor_count+=
         ComputeAllEqualityFactors(state->terms, control->ocb, clause,
                                   state->tmp_store, state->freshvars);
   }
   state->resolv_count+=
      ComputeAllEqnResolvents(state->terms, clause, state->tmp_store,
                              state->freshvars);

   if(control->heuristic_parms.enable_neg_unit_paramod
      ||!ClauseIsUnit(clause)
      ||!ClauseIsNegative(clause))
   { /* Sometime we want to disable paramodulation for negative units */
      PERF_CTR_ENTRY(ParamodTimer);
      if(state->gindices.pm_into_index)
      {
         state->paramod_count+=
            ComputeAllParamodulantsIndexed(state->terms,
                                           control->ocb,
                                           state->freshvars,
                                           tmp_copy,
                                           clause,
                                           state->gindices.pm_into_index,
                                           state->gindices.pm_negp_index,
                                           state->gindices.pm_from_index,
                                           state->tmp_store,
                                           control->heuristic_parms.pm_type);
      }
      else
      {
         state->paramod_count+=
            ComputeAllParamodulants(state->terms, control->ocb,
                                    tmp_copy, clause,
                                    state->processed_pos_rules,
                                    state->tmp_store, state->freshvars,
                                    control->heuristic_parms.pm_type);
         state->paramod_count+=
            ComputeAllParamodulants(state->terms, control->ocb,
                                    tmp_copy, clause,
                                    state->processed_pos_eqns,
                                    state->tmp_store, state->freshvars,
                                    control->heuristic_parms.pm_type);

         if(control->heuristic_parms.enable_neg_unit_paramod && !ClauseIsNegative(clause))
         { /* We never need to try to overlap purely negative clauses! */
            state->paramod_count+=
               ComputeAllParamodulants(state->terms, control->ocb,
                                       tmp_copy, clause,
                                       state->processed_neg_units,
                                       state->tmp_store, state->freshvars,
                                       control->heuristic_parms.pm_type);
         }
         state->paramod_count+=
            ComputeAllParamodulants(state->terms, control->ocb,
                                    tmp_copy, clause,
                                    state->processed_non_units,
                                    state->tmp_store, state->freshvars,
                                    control->heuristic_parms.pm_type);
      }
      PERF_CTR_EXIT(ParamodTimer);
   }
}


/*-----------------------------------------------------------------------
//
// Function: eval_clause_set()
//
//   Add evaluations to all clauses in state->eval_set. Factored out
//   so that batch-processing with e.g. neural networks can be easily
//   integrated.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

void eval_clause_set(ProofState_p state, ProofControl_p control)
{
   Clause_p handle;
   assert(state);
   assert(control);


   for(handle = state->eval_store->anchor->succ;
       handle != state->eval_store->anchor;
       handle = handle->succ)
   {
      HCBClauseEvaluate(control->hcb, handle);
   }

   // TODO: Handle externalWeight evaluations.
   // Have to do it after the for loop because 
   // HCBClauseEvaluate makes space for the evaluations.
   // wfcb can operate with the same signature since Clause_p can also be an array of clauses!
}


/*-----------------------------------------------------------------------
//
// Function: insert_new_clauses()
//
//   Rewrite clauses in state->tmp_store, remove superfluous literals,
//   insert them into state->unprocessed. If an empty clause is
//   detected, return it, otherwise return NULL.
//
// Global Variables: -
//
// Side Effects    : As described.
//
/----------------------------------------------------------------------*/

static Clause_p insert_new_clauses(ProofState_p state, ProofControl_p control)
{
   Clause_p handle;
   long     clause_count;

   state->generated_count+=state->tmp_store->members;
   state->generated_lit_count+=state->tmp_store->literals;
   while((handle = ClauseSetExtractFirst(state->tmp_store)))
   {
      // printf("Inserting: ");
      // ClausePrint(stdout, handle, true);
      // printf("\n");
      if(ClauseQueryProp(handle,CPIsIRVictim))
      {
         assert(ClauseQueryProp(handle, CPLimitedRW));
         ForwardModifyClause(state, control, handle,
                             control->heuristic_parms.forward_context_sr_aggressive||
                             (control->heuristic_parms.backward_context_sr&&
                              ClauseQueryProp(handle,CPIsProcessed)),
                             control->heuristic_parms.condensing_aggressive,
                             FullRewrite);
         ClauseDelProp(handle,CPIsIRVictim);
      }
      ForwardModifyClause(state, control, handle,
                          control->heuristic_parms.forward_context_sr_aggressive||
                          (control->heuristic_parms.backward_context_sr&&
                           ClauseQueryProp(handle,CPIsProcessed)),
                          control->heuristic_parms.condensing_aggressive,
                          control->heuristic_parms.forward_demod);


      if(ClauseIsTrivial(handle))
      {
         ClauseFree(handle);
         continue;
      }




      check_watchlist(&(state->wlindices), state->watchlist,
                      handle, state->archive,
                      control->heuristic_parms.watchlist_is_static,
                      control->heuristic_parms.lambda_demod);
      if(ClauseIsEmpty(handle))
      {
         return handle;
      }

      if(control->heuristic_parms.forward_subsumption_aggressive)
      {
         FVPackedClause_p pclause;

         pclause = ForwardSubsumption(state,
                                      handle,
                                      &(state->aggressive_forward_subsumed_count),
                                      true);
         if(pclause)
         {  // Not subsumed
            FVUnpackClause(pclause);
            ENSURE_NULL(pclause);
         }
         else
         {
            ClauseFree(handle);
            continue;
         }
      }

      if(control->heuristic_parms.er_aggressive &&
         control->heuristic_parms.er_varlit_destructive &&
         (clause_count =
          ClauseERNormalizeVar(state->terms,
                               handle,
                               state->tmp_store,
                               state->freshvars,
                               control->heuristic_parms.er_strong_destructive)))
      {
         state->other_redundant_count += clause_count;
         state->resolv_count += clause_count;
         state->generated_count += clause_count;
         continue;
      }
      if(control->heuristic_parms.split_aggressive &&
         (clause_count = ControlledClauseSplit(state->definition_store,
                                               handle,
                                               state->tmp_store,
                                               control->heuristic_parms.split_clauses,
                                               control->heuristic_parms.split_method,
                                               control->heuristic_parms.split_fresh_defs)))
      {
         state->generated_count += clause_count;
         continue;
      }
      state->non_trivial_generated_count++;
      ClauseDelProp(handle, CPIsOriented);
      if(!control->heuristic_parms.select_on_proc_only)
      {
         DoLiteralSelection(control, handle);
      }
      else
      {
         EqnListDelProp(handle->literals, EPIsSelected);
      }
      handle->create_date = state->proc_non_trivial_count;
      if(ProofObjectRecordsGCSelection)
      {
         ClausePushDerivation(handle, DCCnfEvalGC, NULL, NULL);
      }
//      HCBClauseEvaluate(control->hcb, handle);

      ClauseSetInsert(state->eval_store, handle);
   }
   eval_clause_set(state, control);

   while((handle = ClauseSetExtractFirst(state->eval_store)))
   {
      ClauseDelProp(handle, CPIsOriented);
      DocClauseQuoteDefault(6, handle, "eval");

      rlstate.unprocessedWeightSum += (long long) ClauseStandardWeight(handle);
      ClauseSetInsert(state->unprocessed, handle);
   }
   return NULL;
}


/*-----------------------------------------------------------------------
//
// Function: replacing_inferences()
//
//   Perform the inferences that replace a clause by another:
//   Destructive equality-resolution and/or splitting.
//
//   Returns NULL if clause was replaced, the empty clause if this
//   produced an empty clause, and the original clause otherwise
//
// Global Variables: -
//
// Side Effects    : May insert new clauses into state. May destroy
//                   pclause (in which case it gets rid of the container)
//
/----------------------------------------------------------------------*/

Clause_p replacing_inferences(ProofState_p state, ProofControl_p
                              control, FVPackedClause_p pclause)
{
   long     clause_count;
   Clause_p res = pclause->clause;

   if(problemType == PROBLEM_HO && ImmediateClausification(res, state->tmp_store, state->archive, state->freshvars, control->heuristic_parms.fool_unroll))
   {
      pclause->clause = NULL;
   }
   else
   if(control->heuristic_parms.er_varlit_destructive &&
      (clause_count =
       ClauseERNormalizeVar(state->terms,
                            pclause->clause,
                            state->tmp_store,
                            state->freshvars,
                            control->heuristic_parms.er_strong_destructive)))
   {
      state->other_redundant_count += clause_count;
      state->resolv_count += clause_count;
      pclause->clause = NULL;
   }
   else if(ControlledClauseSplit(state->definition_store,
                                 pclause->clause, state->tmp_store,
                                 control->heuristic_parms.split_clauses,
                                 control->heuristic_parms.split_method,
                                 control->heuristic_parms.split_fresh_defs))
   {
      pclause->clause = NULL;
   }

   if(!pclause->clause)
   {  /* ...then it has been destroyed by one of the above methods,
       * which may have put some clauses into tmp_store. */
      FVUnpackClause(pclause);

      res = insert_new_clauses(state, control);
   }
   return res;
}


/*-----------------------------------------------------------------------
//
// Function: cleanup_unprocessed_clauses()
//
//   Perform maintenenance operations on state->unprocessed, depending
//   on parameters in control:
//   - Remove orphaned clauses
//   - Simplify all unprocessed clauses
//   - Reweigh all unprocessed clauses
//   - Delete "bad" clauses to avoid running out of memories.
//
//   Simplification can find the empty clause, which is then
//   returned.
//
// Global Variables: -
//
// Side Effects    : As described above.
//
/----------------------------------------------------------------------*/

static Clause_p cleanup_unprocessed_clauses(ProofState_p state,
                                            ProofControl_p control)
{
   long long current_storage;
   unsigned long back_simplified;
   long tmp, tmp2;
   long target_size;
   Clause_p unsatisfiable = NULL;

   back_simplified = state->backward_subsumed_count
      +state->backward_rewritten_count;

   if((back_simplified-state->filter_orphans_base)
      > control->heuristic_parms.filter_orphans_limit)
   {
      tmp = ClauseSetDeleteOrphans(state->unprocessed);
      if(OutputLevel)
      {
         fprintf(GlobalOut,
                 "# Deleted %ld orphaned clauses (remaining: %ld)\n",
                 tmp, state->unprocessed->members);
      }
      state->other_redundant_count += tmp;
      state->filter_orphans_base = back_simplified;
   }


   if((state->processed_count-state->forward_contract_base)
      > control->heuristic_parms.forward_contract_limit)
   {
      tmp = state->unprocessed->members;
      unsatisfiable =
         ForwardContractSet(state, control,
                            state->unprocessed, false, FullRewrite,
                            &(state->other_redundant_count), true);
      if(unsatisfiable)
      {
         PStackPushP(state->extract_roots, unsatisfiable);
      }
      if(OutputLevel)
      {
         fprintf(GlobalOut,
                 "# Special forward-contraction deletes %ld clauses"
                 "(remaining: %ld) \n",
                 tmp - state->unprocessed->members,
                 state->unprocessed->members);
      }

      if(unsatisfiable)
      {
         return unsatisfiable;
      }
      state->forward_contract_base = state->processed_count;
      OUTPRINT(1, "# Reweighting unprocessed clauses...\n");
      ClauseSetReweight(control->hcb,  state->unprocessed);
   }

   current_storage  = ProofStateStorage(state);
   if(current_storage > control->heuristic_parms.delete_bad_limit)
   {
      target_size = state->unprocessed->members/2;
      tmp = ClauseSetDeleteOrphans(state->unprocessed);
      tmp2 = HCBClauseSetDeleteBadClauses(control->hcb,
                                          state->unprocessed,
                                          target_size);
      state->non_redundant_deleted += tmp;
      if(OutputLevel)
      {
         fprintf(GlobalOut,
                 "# Deleted %ld orphaned clauses and %ld bad "
                 "clauses (prover may be incomplete now)\n",
                 tmp, tmp2);
      }
      if(tmp2)
      {
         state->state_is_complete = false;
      }
      TBGCCollect(state->terms);
      current_storage = ProofStateStorage(state);
   }
   return unsatisfiable;
}

/*-----------------------------------------------------------------------
//
// Function: SATCheck()
//
//   Create ground (or pseudo-ground) instances of the clause set,
//   hand them to a SAT solver, and check then for unsatisfiability.
//
// Global Variables:
//
// Side Effects    :
//
/----------------------------------------------------------------------*/

Clause_p SATCheck(ProofState_p state, ProofControl_p control)
{
   Clause_p     empty = NULL;
   ProverResult res;
   double
      base_time,
      preproc_time = 0.0,
      enc_time     = 0.0,
      solver_time  = 0.0;

   if(control->heuristic_parms.sat_check_normalize)
   {
      //printf("# Cardinality of unprocessed: %ld\n",
      //        ClauseSetCardinality(state->unprocessed));
      base_time = GetTotalCPUTime();
      printf("SATCHECK SATCHECK SATCHECK SATCHECK SATCHECK #########\n");
      empty = ForwardContractSetReweight(state, control, state->unprocessed,
                                       false, 2,
                                       &(state->proc_trivial_count));
      // printf("# ForwardContraction done\n");
      preproc_time = (GetTotalCPUTime()-base_time);
   }
   if(!empty)
   {
      SatClauseSet_p set = SatClauseSetAlloc();

      // printf("# SatCheck() %ld, %ld..\n",
      //state->proc_non_trivial_count,
      //ProofStateCardinality(state));

      base_time = GetTotalCPUTime();
      SatClauseSetImportProofState(set, state,
                                   control->heuristic_parms.sat_check_grounding,
                                   control->heuristic_parms.sat_check_normconst);

      enc_time = (GetTotalCPUTime()-base_time);
      //printf("# SatCheck()..imported\n");

      base_time = GetTotalCPUTime();
      res = SatClauseSetCheckUnsat(set, &empty, control->solver,
                                   control->heuristic_parms.sat_check_decision_limit);
      ProofControlResetSATSolver(control);
      solver_time = (GetTotalCPUTime()-base_time);
      state->satcheck_count++;

      state->satcheck_preproc_time  += preproc_time;
      state->satcheck_encoding_time += enc_time;
      state->satcheck_solver_time   += solver_time;
      if(res == PRUnsatisfiable)
      {
         state->satcheck_success++;
         state->satcheck_full_size = SatClauseSetCardinality(set);
         state->satcheck_actual_size = SatClauseSetNonPureCardinality(set);
         state->satcheck_core_size = SatClauseSetCoreSize(set);

         state->satcheck_preproc_stime  += preproc_time;
         state->satcheck_encoding_stime += enc_time;
         state->satcheck_solver_stime   += solver_time;
      }
      else if(res == PRSatisfiable)
      {
         state->satcheck_satisfiable++;
      }
      SatClauseSetFree(set);
   }

   return empty;
}

#ifdef PRINT_SHARING

/*-----------------------------------------------------------------------
//
// Function: print_sharing_factor()
//
//   Determine the sharing factor and print it. Potentially expensive,
//   only useful for manual analysis.
//
// Global Variables:
//
// Side Effects    :
//
/----------------------------------------------------------------------*/

static void print_sharing_factor(ProofState_p state)
{
   long shared, unshared;
   shared = TBTermNodes(state->terms);
   unshared = ClauseSetGetTermNodes(state->tmp_store)+
      ClauseSetGetTermNodes(state->processed_pos_rules)+
      ClauseSetGetTermNodes(state->processed_pos_eqns)+
      ClauseSetGetTermNodes(state->processed_neg_units)+
      ClauseSetGetTermNodes(state->processed_non_units)+
      ClauseSetGetTermNodes(state->unprocessed);

   fprintf(GlobalOut, "\n#        GClauses   NClauses    NShared  "
           "NUnshared    TShared  TUnshared TSharinF   \n");
   fprintf(GlobalOut, "# grep %10ld %10ld %10ld %10ld %10ld %10ld %10.3f\n",
           state->generated_count - state->backward_rewritten_count,
           state->tmp_store->members,
           ClauseSetGetSharedTermNodes(state->tmp_store),
           ClauseSetGetTermNodes(state->tmp_store),
           shared,
           unshared,
           (float)unshared/shared);
}
#endif


#ifdef PRINT_RW_STATE

/*-----------------------------------------------------------------------
//
// Function: print_rw_state()
//
//   Print the system (R,E,NEW), e.g. the two types of demodulators
//   and the newly generated clauses.
//
// Global Variables: -
//
// Side Effects    : Output
//
/----------------------------------------------------------------------*/

void print_rw_state(ProofState_p state)
{
   char prefix[20];

   sprintf(prefix, "RWD%09ld_R: ",state->proc_non_trivial_count);
   ClauseSetPrintPrefix(GlobalOut,prefix,state->processed_pos_rules);
   sprintf(prefix, "RWD%09ld_E: ",state->proc_non_trivial_count);
   ClauseSetPrintPrefix(GlobalOut,prefix,state->processed_pos_eqns);
   sprintf(prefix, "RWD%09ld_N: ",state->proc_non_trivial_count);
   ClauseSetPrintPrefix(GlobalOut,prefix,state->tmp_store);
}

#endif





/*---------------------------------------------------------------------*/
/*                         Exported Functions                          */
/*---------------------------------------------------------------------*/



/*-----------------------------------------------------------------------
//
// Function: ProofControlInit()
//
//   Initialize a proof control cell for a given proof state (with at
//   least axioms and signature) and a set of parameters
//   describing the ordering and heuristics.
//
// Global Variables: -
//
// Side Effects    : Sets specs.
//
/----------------------------------------------------------------------*/

void ProofControlInit(ProofState_p state, ProofControl_p control,
                      HeuristicParms_p params, FVIndexParms_p fvi_params,
                      PStack_p wfcb_defs, PStack_p hcb_defs)
{

   PStackPointer sp;
   Scanner_p in;

   assert(control && control->wfcbs);
   assert(state && state->axioms && state->signature);
   assert(params);
   assert(!control->ocb);
   assert(!control->hcb);

   control->ocb = TOSelectOrdering(state, params,
                                   &(control->problem_specs));

   in = CreateScanner(StreamTypeInternalString,
                      DefaultWeightFunctions,
                      true, NULL, true);
   WeightFunDefListParse(control->wfcbs, in, control->ocb, state);
   DestroyScanner(in);

   for(sp = 0; sp < PStackGetSP(wfcb_defs); sp++)
   {
      in = CreateScanner(StreamTypeOptionString,
                         PStackElementP(wfcb_defs, sp) ,
                         true, NULL, true);
      WeightFunDefListParse(control->wfcbs, in, control->ocb, state);
      DestroyScanner(in);
   }
   in = CreateScanner(StreamTypeInternalString,
                      DefaultHeuristics,
                      true, NULL, true);
   HeuristicDefListParse(control->hcbs, in, control->wfcbs,
                         control->ocb, state);
   AcceptInpTok(in, Fullstop);
   DestroyScanner(in);
   if(!PStackEmpty(hcb_defs))
   {
      params->heuristic_def = SecureStrdup(PStackTopP(hcb_defs));
   }
   for(sp = 0; sp < PStackGetSP(hcb_defs); sp++)
   {
      in = CreateScanner(StreamTypeOptionString,
                         PStackElementP(hcb_defs, sp) ,
                         true, NULL, true);
      HeuristicDefListParse(control->hcbs, in, control->wfcbs,
                            control->ocb, state);
      DestroyScanner(in);
   }
   control->heuristic_parms     = *params;

   control->hcb = GetHeuristic(params->heuristic_name,
                               state,
                               control,
                               params);
   control->fvi_parms           = *fvi_params;
   if(!control->heuristic_parms.split_clauses)
   {
      control->fvi_parms.symbol_slack = 0;
   }
   *params = control->heuristic_parms;
   InitUnifLimits(&control->heuristic_parms);
}


/*-----------------------------------------------------------------------
//
// Function: ProofStateResetProcessedSet()
//
//   Move all clauses from set into state->unprocessed.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

void ProofStateResetProcessedSet(ProofState_p state,
                                 ProofControl_p control,
                                 ClauseSet_p set)
{
   Clause_p handle;
   Clause_p tmpclause;
   bool lambda_demod = control->heuristic_parms.lambda_demod;

   while((handle = ClauseSetExtractFirst(set)))
   {
      if(ClauseQueryProp(handle, CPIsGlobalIndexed))
      {
         GlobalIndicesDeleteClause(&(state->gindices), handle, lambda_demod);
      }
      if(ProofObjectRecordsGCSelection)
      {
         ClausePushDerivation(handle, DCCnfEvalGC, NULL, NULL);
      }
      tmpclause = ClauseFlatCopy(handle);
      ClausePushDerivation(tmpclause, DCCnfQuote, handle, NULL);
      ClauseSetInsert(state->archive, handle);
      handle = tmpclause;
      HCBClauseEvaluate(control->hcb, handle);
      ClauseDelProp(handle, CPIsOriented);
      DocClauseQuoteDefault(6, handle, "move_eval");

      if(control->heuristic_parms.prefer_initial_clauses)
      {
         EvalListChangePriority(handle->evaluations, -PrioLargestReasonable);
      }
      ClauseSetInsert(state->unprocessed, handle);
   }
}

/*-----------------------------------------------------------------------
//
// Function: ProofStateMoveSetToTmp()
//
//   Lightweight version of ProofStateResetProcessedSet which simply
//   moves all clauses from set to tmp_store without reevaluating
//   clause evaluation features.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

void ProofStateMoveSetToTmp(ProofState_p state,
                            ProofControl_p control,
                            ClauseSet_p set)
{
   Clause_p handle;

   while((handle = ClauseSetExtractFirst(set)))
   {
      if(ClauseQueryProp(handle, CPIsGlobalIndexed))
      {
         GlobalIndicesDeleteClause(&(state->gindices), handle, control->heuristic_parms.lambda_demod);
      }
      ClauseDelProp(handle, CPIsOriented);
      ClauseSetInsert(state->tmp_store, handle);
   }
}


/*-----------------------------------------------------------------------
//
// Function: ProofStateResetProcessed()
//
//   Move all clauses from the processed clause sets to unprocessed.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

void ProofStateResetProcessed(ProofState_p state, ProofControl_p control)
{
   ProofStateResetProcessedSet(state, control, state->processed_pos_rules);
   ProofStateResetProcessedSet(state, control, state->processed_pos_eqns);
   ProofStateResetProcessedSet(state, control, state->processed_neg_units);
   ProofStateResetProcessedSet(state, control, state->processed_non_units);
}

/*-----------------------------------------------------------------------
//
// Function: ProofStateMoveToTmpStore()
//
//   Move all clauses from the processed clause sets to tmp store.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

void ProofStateMoveToTmpStore(ProofState_p state, ProofControl_p control)
{
   ProofStateMoveSetToTmp(state, control, state->processed_pos_rules);
   ProofStateMoveSetToTmp(state, control, state->processed_pos_eqns);
   ProofStateMoveSetToTmp(state, control, state->processed_neg_units);
   ProofStateMoveSetToTmp(state, control, state->processed_non_units);
}


/*-----------------------------------------------------------------------
//
// Function: fvi_param_init()
//
//   Initialize the parameters for all feature vector indices in
//   state.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

void fvi_param_init(ProofState_p state, ProofControl_p control)
{
   long symbols;
   PermVector_p perm;
   FVCollect_p  cspec;

   state->fvi_initialized = true;
   state->original_symbols = state->signature->f_count;

   symbols = MIN(state->original_symbols+control->fvi_parms.symbol_slack,
                 control->fvi_parms.max_symbols);

   // printf("### Symbols: %ld\n", symbols);
   switch(control->fvi_parms.cspec.features)
   {
   case FVIBillFeatures:
         cspec = BillFeaturesCollectAlloc(state->signature, symbols*2+2);
         break;
   case FVIBillPlusFeatures:
         cspec = BillPlusFeaturesCollectAlloc(state->signature, symbols*2+4);
         break;
   case FVIACFold:
         // printf("# FVIACFold\n");
         cspec = FVCollectAlloc(FVICollectFeatures,
                                true,
                                0,
                                symbols*2+2,
                                2,
                                0,
                                symbols,
                                symbols+2,
                                0,
                                symbols,
                                0,0,0,
                                0,0,0);
         break;
   case FVIACStagger:
         cspec = FVCollectAlloc(FVICollectFeatures,
                                true,
                                0,
                                symbols*2+2,
                                2,
                                0,
                                2*symbols,
                                2,
                                2+symbols,
                                2*symbols,
                                0,0,0,
                                0,0,0);
         break;
   case FVICollectFeatures:
         cspec = FVCollectAlloc(control->fvi_parms.cspec.features,
                                control->fvi_parms.cspec.use_litcount,
                                control->fvi_parms.cspec.ass_vec_len,
                                symbols,
                                control->fvi_parms.cspec.pos_count_base,
                                control->fvi_parms.cspec.pos_count_offset,
                                control->fvi_parms.cspec.pos_count_mod,
                                control->fvi_parms.cspec.neg_count_base,
                                control->fvi_parms.cspec.neg_count_offset,
                                control->fvi_parms.cspec.neg_count_mod,
                                control->fvi_parms.cspec.pos_depth_base,
                                control->fvi_parms.cspec.pos_depth_offset,
                                control->fvi_parms.cspec.pos_depth_mod,
                                control->fvi_parms.cspec.neg_depth_base,
                                control->fvi_parms.cspec.neg_depth_offset,
                                control->fvi_parms.cspec.neg_depth_mod);

         break;
   default:
         cspec = FVCollectAlloc(control->fvi_parms.cspec.features,
                                0,
                                0,
                                0,
                                0, 0, 0,
                                0, 0, 0,
                                0, 0, 0,
                                0, 0, 0);
         break;
   }
   cspec->max_symbols=symbols;
   state->fvi_cspec = cspec;

   perm = PermVectorCompute(state->axioms,
                            cspec,
                            control->fvi_parms.eliminate_uninformative);
   if(control->fvi_parms.cspec.features != FVINoFeatures)
   {
      state->processed_non_units->fvindex =
         FVIAnchorAlloc(cspec, PermVectorCopy(perm));
      state->processed_pos_rules->fvindex =
         FVIAnchorAlloc(cspec, PermVectorCopy(perm));
      state->processed_pos_eqns->fvindex =
         FVIAnchorAlloc(cspec, PermVectorCopy(perm));
      state->processed_neg_units->fvindex =
         FVIAnchorAlloc(cspec, PermVectorCopy(perm));
      if(state->watchlist)
      {
         state->watchlist->fvindex =
            FVIAnchorAlloc(cspec, PermVectorCopy(perm));
         //ClauseSetNewTerms(state->watchlist, state->terms);
      }
   }
   state->def_store_cspec = FVCollectAlloc(FVICollectFeatures,
                                           true,
                                           0,
                                           symbols*2+2,
                                           2,
                                           0,
                                           symbols,
                                           symbols+2,
                                           0,
                                           symbols,
                                           0,0,0,
                                           0,0,0);
   state->definition_store->def_clauses->fvindex =
      FVIAnchorAlloc(state->def_store_cspec, perm);
}



/*-----------------------------------------------------------------------
//
// Function: ProofStateInit()
//
//   Given a proof state with axioms and a heuristic parameter
//   description, initialize the ProofStateCell, i.e. generate the
//   HCB, the ordering, and evaluate the axioms and put them in the
//   unprocessed list.
//
// Global Variables:
//
// Side Effects    :
//
/----------------------------------------------------------------------*/

void ProofStateInit(ProofState_p state, ProofControl_p control)
{
   Clause_p handle, new;
   HCB_p    tmphcb;
   PStack_p traverse;
   Eval_p   cell;

   rlstate.state = state;

   OUTPRINT(1, "# Initializing proof state\n");

   assert(ClauseSetEmpty(state->processed_pos_rules));
   assert(ClauseSetEmpty(state->processed_pos_eqns));
   assert(ClauseSetEmpty(state->processed_neg_units));
   assert(ClauseSetEmpty(state->processed_non_units));

   if(!state->fvi_initialized)
   {
      fvi_param_init(state, control);
   }
   ProofStateInitWatchlist(state, control->ocb);

   tmphcb = GetHeuristic("Uniq", state, control, &(control->heuristic_parms));
   assert(tmphcb);
   ClauseSetReweight(tmphcb, state->axioms);

   traverse =
      EvalTreeTraverseInit(PDArrayElementP(state->axioms->eval_indices,0),0);

   while((cell = EvalTreeTraverseNext(traverse, 0)))
   {
      handle = cell->object;
      new = ClauseCopy(handle, state->terms);

      ClauseSetProp(new, CPInitial);
      check_watchlist(&(state->wlindices), state->watchlist,
                      new, state->archive,
                      control->heuristic_parms.watchlist_is_static,
                      control->heuristic_parms.lambda_demod);
      HCBClauseEvaluate(control->hcb, new);
      DocClauseQuoteDefault(6, new, "eval");
      ClausePushDerivation(new, DCCnfQuote, handle, NULL);
      if(ProofObjectRecordsGCSelection)
      {
         ClausePushDerivation(new, DCCnfEvalGC, NULL, NULL);
      }
      if(control->heuristic_parms.prefer_initial_clauses)
      {
         EvalListChangePriority(new->evaluations, -PrioLargestReasonable);
      }
      ClauseSetInsert(state->unprocessed, new);
   }
   //OUTPRINT(1, "# Initializing proof state (3)\n");
   ClauseSetMarkSOS(state->unprocessed, control->heuristic_parms.use_tptp_sos);
   // printf("Before EvalTreeTraverseExit\n");
   EvalTreeTraverseExit(traverse);

   if(control->heuristic_parms.ac_handling!=NoACHandling)
   {
      if(OutputLevel)
      {
         fprintf(GlobalOut, "# Scanning for AC axioms\n");
      }
      control->ac_handling_active = ClauseSetScanAC(state->signature,
                                                    state->unprocessed);
      if(OutputLevel)
      {
         SigPrintACStatus(GlobalOut, state->signature);
         if(control->ac_handling_active)
         {
            fprintf(GlobalOut, "# AC handling enabled\n");
         }
      }
   }

   GlobalIndicesFreeIndices(&(state->gindices)); // if we are reinstantiating
   GlobalIndicesInit(&(state->gindices),
                     state->signature,
                     control->heuristic_parms.rw_bw_index_type,
                     control->heuristic_parms.pm_from_index_type,
                     control->heuristic_parms.pm_into_index_type,
                     control->heuristic_parms.ext_rules_max_depth);
}




long long timeInMicroSeconds() {
    struct timeval tv;

    gettimeofday(&tv,NULL);
    return (((long long)tv.tv_sec)*1000000)+(tv.tv_usec);
}

long long timerStart(){
   return timeInMicroSeconds();
}

void timerEnd(long long startTime, long long* destination){
   *destination += (timeInMicroSeconds() - startTime);
}



void initRL(){
   printf("Initializing Reinforcement Learning...\n");
   MCTSRoot = makeRoot();
   MCTSChosen = MCTSRoot;
   criticModel = LoadModel("./critic.torchscript"); // ASSUMPTION!!! The critic model is in the working directory.

   // char* state_pipe_path = (state_pipe_path = getenv("E_RL_STATEPIPE_PATH")) ? state_pipe_path : "/tmp/StatePipe1";
   // char* action_pipe_path = (action_pipe_path = getenv("E_RL_ACTIONPIPE_PATH")) ? action_pipe_path : "/tmp/ActionPipe1";
   // char* reward_pipe_path = (reward_pipe_path = getenv("E_RL_REWARDPIPE_PATH")) ? reward_pipe_path : "/tmp/RewardPipe1";

   // printf("State Pipe Path: %s\n", state_pipe_path);
   // printf("Action Pipe Path: %s\n", action_pipe_path);
   // printf("Reward Pipe Path: %s\n", reward_pipe_path);

   // StatePipe = open(state_pipe_path, O_WRONLY);
   // ActionPipe = open(action_pipe_path, O_RDONLY);
   // RewardPipe = open(reward_pipe_path, O_WRONLY);
   // sync_num = -1; // -1 because it is incremented in each call to sendRLState()


   // Initialize rlstate
   rlstate.numEverProcessed = 0;
   rlstate.numProcessed = 0;
   rlstate.numUnprocessed = 0;
   rlstate.processedWeightSum = 0;
   rlstate.unprocessedWeightSum = 0;
   // rlstate.state = state; // not feasible because eprover.c does not have access to the state yet.

   rl_weight_tracking = ClauseSetAlloc();
}


void checkWeightTracking(ProofState_p state, char* caption, int which){

   if (which == 0 || which == 2){
      long long  pWeight = ClauseSetStandardWeight(state->processed_neg_units) +
                           ClauseSetStandardWeight(state->processed_non_units) +
                           ClauseSetStandardWeight(state->processed_pos_eqns) +
                           ClauseSetStandardWeight(state->processed_pos_rules);
      if (pWeight != rlstate.processedWeightSum){
         printf("Processed tracking failure at %s: (%lld != %llu)\n", caption, pWeight, rlstate.processedWeightSum);
         exit(1);
      }
      else{
         printf("Processed tracked successfully at %s: (%lld)\n", caption, pWeight);
      }
   }

   if (which == 1 || which == 2){
      long long uWeight = ClauseSetStandardWeight(state->unprocessed);
      if (uWeight != rlstate.unprocessedWeightSum){
         printf("Unprocessed tracking failure at %s: (%lld != %llu)\n", caption, uWeight, rlstate.unprocessedWeightSum);
         exit(1);
      }
      else{
         printf("Unprocessed tracked successfully at %s: (%lld)\n", caption, uWeight);
      }
   }

}


void printRLState(RLProofStateCell state){
   float pweight = (float)state.processedWeightSum / (float)state.numProcessed;
   pweight = (isnan(pweight)) ? -1.0 : pweight;

   float uweight = (float)state.unprocessedWeightSum / (float)state.numUnprocessed;
   uweight = (isnan(uweight)) ? -1.0 : uweight;

   // printf("uweight = sum / len: %f = %llu / %lu\n", uweight,state.unprocessedWeightSum, state.numUnprocessed);
   // printf("pweight = sum / len: %f = %llu / %lu\n", pweight,state.processedWeightSum, state.numProcessed);
   printf("RL State: (%lu, %lu, %lu, %f, %f)\n", state.numEverProcessed, state.numProcessed, state.numUnprocessed, pweight, uweight);
}

void sendRLState(RLProofStateCell state){
   long long start = timerStart();
   // printf("Sending RL State...\n");
   // sync_num++;

   // float pweight = (float)state.processedWeightSum / (float) state.numProcessed;
   // pweight = (isnan(pweight)) ? -1.0 : pweight;

   // float uweight = (float)state.unprocessedWeightSum / (float) state.numUnprocessed;
   // uweight = (isnan(uweight)) ? -1.0 : uweight;

   // write(StatePipe, &(sync_num), sizeof(int));
   // write(StatePipe, &(state.numEverProcessed), sizeof(size_t));
   // write(StatePipe, &(state.numProcessed), sizeof(size_t));
   // write(StatePipe, &(state.numUnprocessed), sizeof(size_t));
   // write(StatePipe, &pweight, sizeof(float));
   // write(StatePipe, &uweight, sizeof(float));

   timerEnd(start, &statePipeTimeSpent);
}


// Have to remember to also do the state normalization.
Array RLstateToArray(RLProofStateCell state){
   float* data = (float*) malloc(sizeof(float)*5);

   // Current python normalization code...
   //  s = state / torch.tensor([40_000, 9_000, 1_300_000, 100, 200], dtype=torch.float)

   data[0] = (float) state.numEverProcessed / 40000.0;
   data[1] = (float) state.numProcessed / 9000.0;
   data[2] = (float) state.numUnprocessed / 1300000.0;
   data[3] = (float) ((state.processedWeightSum / (float) state.numProcessed) / 100.0);
   data[4] = (float) ((state.unprocessedWeightSum / (float) state.numUnprocessed) / 200.0);

   return createArray(data, 5, FLOAT, true);
}

float invokeCritic(RLProofStateCell state){
   time_before_critic = myGetTime();
   Array arr = RLstateToArray(state);
   time_after_making_array = myGetTime();

   // Array output = RunModel(criticModel, arr);
   
   // float evaluation = arrayItem(output).f;


   time_after_conversion_to_tensor = myGetTime();
   time_after_critic_running = myGetTime();
   time_after_conversion_to_array = myGetTime();

   float evaluation = -1*(
      ((float*)arr.data)[0] + 
      ((float*)arr.data)[1] + 
      ((float*)arr.data)[2] + 
      ((float*)arr.data)[3] + 
      ((float*)arr.data)[4]
   );

   // freeArray(arr);
   // freeArray(output);

   // Dangerous not to free, but it was causing issues and it's probably fine 
   // because it's only 5 floats and it's not like we're running out of memory
   // and it's not like we're going to be running this for a long time
   // so it's probably fine.
   // ^^^^ Rationalization provided by Copilot lol

   return evaluation;

   // return 10.0 - (state.numUnprocessed / 100.0);
}


int recvRLAction(){
   long long start = timerStart();
   // char buff[200];

   // printf("----Reading sync_num_remote\n");
   // int x = read(ActionPipe, buff, sizeof(int));
   // int sync_num_remote = *((int*)buff);

   // // printf("----Reading actual action\n");
   // read(ActionPipe, buff, sizeof(int));
   // int action = *((int*)buff);
   // // printf("Action received: %d\n", action);

   // // printf("----assertion\n");
   // assert(sync_num_remote == sync_num);
   // assert(action >= 0 && action < 20);

   // int action = rand() % 20;


   bool InSmartPhase = (rlstate.numEverProcessed > 0 && rlstate.numEverProcessed < 100) && !smartPhaseKilled;
   int numSimulations = 150;

   int action;
   if (!MCTS_SIM && InSmartPhase){
      action = MCTSSearch(MCTSChosen, numSimulations);
      printf("After search...\n");
   }

   if (MCTS_SIM){
      printf("Child recvRLAction\n");

      // Turn off stdout for simulator...
      // OutputLevel = 0;

      // phase=1 means we are in the smart phase, phase=2 means we are in the random phase, phase=3 means we are done.
      int phase = MCTS_SIM_STEPS < MCTSSimulated->state->len ? 1 : (MCTS_SIM_STEPS < MAX_STATE_LEN ? 2 : 3);
      
      // If eprover encounters its CPU_LIMIT, then we need to stop.
      if (TimeIsUp || phase == 3){
         endSimulation(invokeCritic(rlstate));
      }

      // Pick action according to state.
      else if (phase == 1){
         action = MCTSSimulated->state->cef_choices[MCTS_SIM_STEPS];
      }
      // If at the end of state, then simulate for a while.
      else if (phase == 2){
         action = rand() % AvailableActions(MCTSSimulated); // INCORRECT!!! but fine for now becuase it's a constant...
      }
      else{
         printf("ERROR: Should not be here\n");
         exit(1);
      }

      GCS_Times[MCTS_SIM_STEPS] = myGetTime();
      MCTS_SIM_STEPS++;
   }
   else{
      printf("Parent recvRLAction\n");

      if(InSmartPhase){
         MCTSChosen = MCTSChosen->children[action];
         MCTSStateShift(MCTSChosen);

         float proofProb = MCTSChosen->totalReward / MCTSChosen->numVisits;
         printf("MCTS Info   : %f, %d, %f\n", MCTSChosen->totalReward , MCTSChosen->numVisits, proofProb);
         printf("Received MCTS Action: %d\n", action);
         
         if (proofProb > 0.95 && MCTSChosen->numVisits > (numSimulations * 0.5)){
            printf("Proof likely!: Let's go fast\n");
            smartPhaseKilled = true;
         }
      }
      else{
         printf("Random action\n");
         action = rand() % AvailableActions(MCTSChosen);
      }
   }

   timerEnd(start, &actionPipeTimeSpent);

   // printf("Action received: %d\n", action);
   return action;
}


void sendRLReward(float reward){
   long long start = timerStart();
   // printf("Sending RL Reward\n");
   // write(RewardPipe, &(sync_num), sizeof(int));
   // write(RewardPipe, &reward, sizeof(float));

   // if (reward == 1.0){
   //    printf("RL thinks proof is found!\n");
   // }
   // printf("RL Reward: %f\n", reward);

   timerEnd(start, &rewardPipeTimeSpent);
}

Clause_p customized_hcb_select(HCB_p hcb, ClauseSet_p set)
{
   Clause_p clause;

   clause = ClauseSetFindBest(set, hcb->current_eval);
   while(clause && ClauseIsOrphaned(clause))
   {
      rlstate.unprocessedWeightSum -= (long long) ClauseStandardWeight(clause);
      ClauseSetExtractEntry(clause);
      ClauseFree(clause);
      clause = ClauseSetFindBest(set, hcb->current_eval);
   }
   hcb->select_count++;
   while(hcb->select_count ==
         PDArrayElementInt(hcb->select_switch,hcb->current_eval))
   {
      hcb->current_eval++;
   }
   if(hcb->current_eval == hcb->wfcb_no)
   {
      hcb->select_count = 0;
      hcb->current_eval = 0;
   }
   return clause;
}





void PrintArchive(ProofState_p state){

   printf("######################################\n");
   for(Clause_p handle=state->archive->anchor->succ; handle != state->archive->anchor; handle=handle->succ){
      ClausePrint(GlobalOut, handle, true);
      printf(" %ld ", handle->given_clause_selection_index);
      printf(" %d ", ClauseIsEvalGC(handle));
      printf(" %d ", ClauseHasEvalGC(handle));
      printf(" %d \n", ClauseQueryProp(handle, CPIsProofClause));
   }
   printf("######################################\n");

}



/*-----------------------------------------------------------------------
//
// Function: ProcessClause()
//
//   Select an unprocessed clause, process it. Return pointer to empty
//   clause if it can be derived, NULL otherwise. This is the core of
//   the main proof procedure.
//
// Global Variables: -
//
// Side Effects    : Everything ;-)
//
/----------------------------------------------------------------------*/

Clause_p ProcessClause(ProofState_p state, ProofControl_p control,
                       long answer_limit)
{


   printf("Number of CEFs: %d\n", control->hcb->wfcb_no);
   Clause_p         clause, resclause, tmp_copy, empty, arch_copy = NULL;
   FVPackedClause_p pclause;
   SysDate          clausedate;
   static bool first_time = true;

   // int trackingWhich = 2;

   state->RLTimeSpent_statePipe = statePipeTimeSpent;
   state->RLTimeSpent_actionPipe = actionPipeTimeSpent;
   state->RLTimeSpent_rewardPipe = rewardPipeTimeSpent;
   state->RLTimeSpent_prep = statePrepTimeSpent;

   bool not_in_presaturation_interreduction = (control->heuristic_parms.selection_strategy != SelectNoGeneration);

   //////// Jack McKeown's Reinforcement Learning Idea ///////////////////
   long long startTime = timerStart();
   rlstate.numProcessed = ClauseSetCardinality(state->processed_neg_units) \
                        + ClauseSetCardinality(state->processed_non_units) \
                        + ClauseSetCardinality(state->processed_pos_eqns) \
                        + ClauseSetCardinality(state->processed_pos_rules);
   rlstate.numUnprocessed = ClauseSetCardinality(state->unprocessed);


   if(first_time && not_in_presaturation_interreduction){
      first_time = false;
      rlstate.processedWeightSum =  ClauseSetStandardWeight(state->processed_neg_units) +
                                    ClauseSetStandardWeight(state->processed_non_units) +
                                    ClauseSetStandardWeight(state->processed_pos_eqns)  +
                                    ClauseSetStandardWeight(state->processed_pos_rules);

      rlstate.unprocessedWeightSum = ClauseSetStandardWeight(state->unprocessed);

      printf("Initialized processed/unprocessed weights for tracking: (%llu, %llu)\n", rlstate.processedWeightSum, rlstate.unprocessedWeightSum);
      rlstate.numEverProcessed += 1;
   }
   else if(not_in_presaturation_interreduction){
      // Comment for better performance, once you're sure there are no issues with the tracking...
      // checkWeightTracking(state, "MainCheck", trackingWhich);
      rlstate.numEverProcessed += 1;
   }

   timerEnd(startTime, &statePrepTimeSpent);

   sendRLState(rlstate);

   size_t action = recvRLAction();
   control->hcb->current_eval = action;

   ///////////////////////////////////////////////////////////////////////

   // clause = control->hcb->hcb_select(control->hcb,
   //                                   state->unprocessed);

   printf("Just before customized_hcb_select...\n");
   clause = customized_hcb_select(control->hcb, state->unprocessed);
   printf("Way before: %ld\n", clause->given_clause_selection_index);
   if (not_in_presaturation_interreduction){
      if (*(clause->given_clause_selection_index_p) < 0){
         clause->given_clause_selection_index = rlstate.numEverProcessed-1;
         *(clause->given_clause_selection_index_p) = rlstate.numEverProcessed-1;
      }
   }
   else{
      clause->given_clause_selection_index = -2;
      *(clause->given_clause_selection_index_p) = -2;
   }
   
   if (not_in_presaturation_interreduction){
      printRLState(rlstate);
      printf("CEF Choice: %lu\n", action);
      printf("Given Clause: ");
      ClausePrint(stdout, clause, true);
      printf("\nSet given_clause_selection_index to %ld\n", clause->given_clause_selection_index);
   }

   if(!clause)
   {
      sendRLReward(0.0);
      printf("!clause\n");
      return NULL;
   }
   if(OutputLevel==1)
   {
      putc('#', GlobalOut);
   }
   assert(clause);



   if(not_in_presaturation_interreduction) rlstate.unprocessedWeightSum -= (long long) ClauseStandardWeight(clause);
   ClauseSetExtractEntry(clause);
   ClauseRemoveEvaluations(clause);
   // Orphans have been excluded during selection now

   ClauseSetProp(clause, CPIsProcessed);
   state->processed_count++;

   assert(!ClauseQueryProp(clause, CPIsIRVictim));


   if(ProofObjectRecordsGCSelection)
   {
      printf("\nArchiving clause...\n");
      printf("Before: %ld\n", clause->given_clause_selection_index);
      arch_copy = ClauseArchiveCopy(state->archive, clause);
      // printf("After: %d\n", arch_copy->given_clause_selection_index);
      ClausePrint(stdout, state->archive->anchor->pred, true);
      printf("After: %ld\n", state->archive->anchor->pred->given_clause_selection_index);
      // PrintArchive(state);
   }

   if(!(pclause = ForwardContractClause(state, control,
                                        clause, true,
                                        control->heuristic_parms.forward_context_sr,
                                        control->heuristic_parms.condensing,
                                        FullRewrite)))
   {
      if(arch_copy)
      {
         ClauseSetDeleteEntry(arch_copy);
      }
      sendRLReward(0.0);
      printf("Subsumed I think!\n");
      return NULL;
   }


   if(ClauseIsSemFalse(pclause->clause))
   {
      state->answer_count ++;
      ClausePrintAnswer(GlobalOut, pclause->clause, state);
      PStackPushP(state->extract_roots, pclause->clause);
      if(ClauseIsEmpty(pclause->clause)||
         state->answer_count>=answer_limit)
      {
         clause = FVUnpackClause(pclause);
         ClauseEvaluateAnswerLits(clause);
         sendRLReward(1.0);
         printf("ClauseIsSemFalse!\n");
         return clause;
      }
   }
   assert(ClauseIsSubsumeOrdered(pclause->clause));
   check_ac_status(state, control, pclause->clause);

   document_processing(pclause->clause);
   state->proc_non_trivial_count++;

   printf("After documenting processing...\n");

   resclause = replacing_inferences(state, control, pclause);
   if(!resclause || ClauseIsEmpty(resclause))
   {
      if(resclause)
      {
         PStackPushP(state->extract_roots, resclause);
         sendRLReward(1.0);
      }
      else{
         sendRLReward(0.0);
      }
      
      return resclause;
   }


   check_watchlist(&(state->wlindices), state->watchlist,
                      pclause->clause, state->archive,
                      control->heuristic_parms.watchlist_is_static,
                      control->heuristic_parms.lambda_demod);

   /* Now on to backward simplification. */
   clausedate = ClauseSetListGetMaxDate(state->demods, FullRewrite);

   eliminate_backward_rewritten_clauses(state, control, pclause->clause, &clausedate);


   eliminate_backward_subsumed_clauses(state, pclause,
                                       control->heuristic_parms.lambda_demod);


   eliminate_unit_simplified_clauses(state, pclause->clause,
                                    control->heuristic_parms.lambda_demod);


   eliminate_context_sr_clauses(state, control, pclause->clause,
                                control->heuristic_parms.lambda_demod);


   ClauseSetSetProp(state->tmp_store, CPIsIRVictim);

   clause = pclause->clause;

   ClauseNormalizeVars(clause, state->freshvars);
   tmp_copy = ClauseCopyDisjoint(clause);
   tmp_copy->ident = clause->ident;

   clause->date = clausedate;
   ClauseSetProp(clause, CPLimitedRW);

   if(ClauseIsDemodulator(clause))
   {
      assert(clause->neg_lit_no == 0);
      if(EqnIsOriented(clause->literals))
      {
         TermCellSetProp(clause->literals->lterm, TPIsRewritable);
         state->processed_pos_rules->date = clausedate;
         rlstate.processedWeightSum += ClauseStandardWeight(pclause->clause);
         ClauseSetIndexedInsert(state->processed_pos_rules, pclause);
      }
      else
      {
         state->processed_pos_eqns->date = clausedate;
         rlstate.processedWeightSum += ClauseStandardWeight(pclause->clause);
         ClauseSetIndexedInsert(state->processed_pos_eqns, pclause);
      }
   }
   else if(ClauseLiteralNumber(clause) == 1)
   {
      assert(clause->neg_lit_no == 1);
      rlstate.processedWeightSum += ClauseStandardWeight(pclause->clause);
      ClauseSetIndexedInsert(state->processed_neg_units, pclause);
   }
   else
   {
      rlstate.processedWeightSum += ClauseStandardWeight(pclause->clause);
      ClauseSetIndexedInsert(state->processed_non_units, pclause);
   }


   GlobalIndicesInsertClause(&(state->gindices), clause,
                             control->heuristic_parms.lambda_demod);

   FVUnpackClause(pclause);
   ENSURE_NULL(pclause);
   if(state->watchlist && control->heuristic_parms.watchlist_simplify)
   {
      simplify_watchlist(state, control, clause);
   }
   if(control->heuristic_parms.selection_strategy != SelectNoGeneration)
   {
      generate_new_clauses(state, control, clause, tmp_copy);
   }
   ClauseFree(tmp_copy);
   if(TermCellStoreNodes(&(state->tmp_terms->term_store))>TMPBANK_GC_LIMIT)
   {
      TBGCSweep(state->tmp_terms);
   }
#ifdef PRINT_SHARING
   print_sharing_factor(state);
#endif
#ifdef PRINT_RW_STATE
   print_rw_state(state);
#endif
   if(control->heuristic_parms.detsort_tmpset)
   {
      ClauseSetSort(state->tmp_store, ClauseCmpByStructWeight);
   }
   if((empty = insert_new_clauses(state, control)))
   {
      PStackPushP(state->extract_roots, empty);
      sendRLReward(1.0);
      return empty;
   }
   sendRLReward(0.0);


   return NULL;
}


/*-----------------------------------------------------------------------
//
// Function:  Saturate()
//
//   Process clauses until either the empty clause has been derived, a
//   specified number of clauses has been processed, or the clause set
//   is saturated. Return empty clause (if found) or NULL.
//
// Global Variables: -
//
// Side Effects    : Modifies state.
//
/----------------------------------------------------------------------*/

Clause_p Saturate(ProofState_p state, ProofControl_p control, long
                  step_limit, long proc_limit, long unproc_limit, long
                  total_limit, long generated_limit, long tb_insert_limit,
                  long answer_limit)
{
   Clause_p unsatisfiable = NULL;
   long
      count = 0,
      sat_check_size_limit = control->heuristic_parms.sat_check_size_limit,
      sat_check_step_limit = control->heuristic_parms.sat_check_step_limit,
      sat_check_ttinsert_limit = control->heuristic_parms.sat_check_ttinsert_limit;


   while(!TimeIsUp &&
         !ClauseSetEmpty(state->unprocessed) &&
         step_limit   > count &&
         proc_limit   > ProofStateProcCardinality(state) &&
         unproc_limit > ProofStateUnprocCardinality(state) &&
         total_limit  > ProofStateCardinality(state) &&
         generated_limit > (state->generated_count -
                            state->backward_rewritten_count)&&
         tb_insert_limit > state->terms->insertions &&
         (!state->watchlist||!ClauseSetEmpty(state->watchlist)))
   {
      count++;
      unsatisfiable = ProcessClause(state, control, answer_limit);
      if(unsatisfiable)
      {
         break;
      }
      unsatisfiable = cleanup_unprocessed_clauses(state, control);
      if(unsatisfiable)
      {
         break;
      }
      if(control->heuristic_parms.sat_check_grounding != GMNoGrounding)
      {
         if(ProofStateCardinality(state) >= sat_check_size_limit)
         {
            unsatisfiable = SATCheck(state, control);
            while(sat_check_size_limit <= ProofStateCardinality(state))
            {
               sat_check_size_limit += control->heuristic_parms.sat_check_size_limit;
            }
         }
         else if(state->proc_non_trivial_count >= sat_check_step_limit)
         {
            unsatisfiable = SATCheck(state, control);
            sat_check_step_limit += control->heuristic_parms.sat_check_step_limit;
         }
         else if( state->terms->insertions >= sat_check_ttinsert_limit)
         {
            unsatisfiable = SATCheck(state, control);
            sat_check_ttinsert_limit *=2;
         }
         if(unsatisfiable)
         {
            PStackPushP(state->extract_roots, unsatisfiable);
            break;
         }
      }
   }
   return unsatisfiable;
}




/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/
