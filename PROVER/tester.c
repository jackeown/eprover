/*-----------------------------------------------------------------------

  File  : eprover.c

  Author: Stephan Schulz

  Contents

  Main program for the E equational theorem prover.

  Copyright 1998-2017 by the authors.
  This code is released under the GNU General Public Licence and
  the GNU Lesser General Public License.
  See the file COPYING in the main E directory for details..
  Run "eprover -h" for contact information.

  Created: Tue Jun  9 01:32:15 MET DST 1998 - New.

-----------------------------------------------------------------------*/

#include <clb_defines.h>
#include <clb_regmem.h>
#include <cio_commandline.h>
#include <cio_output.h>
#include <ccl_relevance.h>
#include <cco_proofproc.h>
#include <cco_sine.h>
#include <cio_signals.h>
#include <ccl_unfold_defs.h>
#include <ccl_formulafunc.h>
#include <cco_scheduling.h>
#include <e_version.h>
#include <ccl_rewrite.h>
#include <ccl_pdtrees.h>


/*---------------------------------------------------------------------*/
/*                  Data types                                         */
/*---------------------------------------------------------------------*/

#define NAME         "eprover"

PERF_CTR_DEFINE(SatTimer);

#include <e_options.h>


/*---------------------------------------------------------------------*/
/*                        Global Variables                             */
/*---------------------------------------------------------------------*/

char              *outname = NULL;
char              *watchlist_filename = NULL;
HeuristicParms_p  h_parms;
FVIndexParms_p    fvi_parms;
bool              print_sat = false,
   print_full_deriv = false,
   print_statistics = false,
   filter_sat = false,
   print_rusage = false,
   print_pid = false,
   print_version = false,
   outinfo = false,
   error_on_empty = false,
   no_preproc = false,
   no_eq_unfold = false,
   pcl_full_terms = true,
   indexed_subsumption = true,
   prune_only = false,
   new_cnf = true,
   cnf_only = false,
   inf_sys_complete = true,
   assume_inf_sys_complete = false,
   incomplete = false,
   conjectures_are_questions = false,
   strategy_scheduling = false;
ProofOutput       print_derivation = PONone;
long              proc_training_data;

IOFormat          parse_format = AutoFormat;
long              step_limit = LONG_MAX,
   answer_limit = 1,
   proc_limit = LONG_MAX,
   unproc_limit = LONG_MAX,
   total_limit = LONG_MAX,
   generated_limit = LONG_MAX,
   eqdef_maxclauses = DEFAULT_EQDEF_MAXCLAUSES,
   relevance_prune_level = 0,
   miniscope_limit = 1000;
long long tb_insert_limit = LLONG_MAX;

int eqdef_incrlimit = DEFAULT_EQDEF_INCRLIMIT,
   force_deriv_output = 0;
char              *outdesc = DEFAULT_OUTPUT_DESCRIPTOR,
   *filterdesc = DEFAULT_FILTER_DESCRIPTOR;
PStack_p          wfcb_definitions, hcb_definitions;
char              *sine=NULL;
pid_t              pid = 0;
int               ProblemIsHO = PROBLEM_NOT_INIT;

FunctionProperties free_symb_prop = FPIgnoreProps;

/*---------------------------------------------------------------------*/
/*                      Forward Declarations                           */
/*---------------------------------------------------------------------*/

CLState_p process_options(int argc, char* argv[]);
void print_help(FILE* out);

/*---------------------------------------------------------------------*/
/*                         Internal Functions                          */
/*---------------------------------------------------------------------*/




/*-----------------------------------------------------------------------
//
// Function: parse_spec()
//
//   Allocate proof state, parse input files into it, and check that
//   requested properties are met. Factored out of main for reasons of
//   readability and length.
//
// Global Variables: -
//
// Side Effects    : Memory, input, may terminate with error.
//
/----------------------------------------------------------------------*/

ProofState_p parse_spec(CLState_p state,
                        IOFormat parse_format_local,
                        bool error_on_empty_local,
                        FunctionProperties free_symb_prop_local,
                        long* ax_no)
{
   ProofState_p proofstate;
   Scanner_p in = NULL;
   int i;
   StrTree_p skip_includes = NULL;
   long parsed_ax_no;

   proofstate = ProofStateAlloc(free_symb_prop_local);
   for(i=0; state->argv[i]; i++)
   {
      in = CreateScanner(StreamTypeFile, state->argv[i], true, NULL);
      ScannerSetFormat(in, parse_format_local);
      if(parse_format_local == AutoFormat && in->format == TSTPFormat)
      {
         OutputFormat = TSTPFormat;
         if(DocOutputFormat == no_format)
         {
            DocOutputFormat = tstp_format;
         }
      }
      if(DocOutputFormat==no_format)
      {
         DocOutputFormat = pcl_format;
      }

      FormulaAndClauseSetParse(in, proofstate->axioms,
                               proofstate->f_axioms,
                               proofstate->terms,
                               NULL,
                               &skip_includes);
      CheckInpTok(in, NoToken);
      DestroyScanner(in);
   }
   VERBOUT2("Specification read\n");

   proofstate->has_interpreted_symbols =
      FormulaSetHasInterpretedSymbol(proofstate->f_axioms);
   parsed_ax_no = ProofStateAxNo(proofstate);

   if(error_on_empty_local && (parsed_ax_no == 0))
   {
#ifdef PRINT_SOMEERRORS_STDOUT
      fprintf(GlobalOut, "# Error: Input file contains no clauses or formulas\n");
      TSTPOUT(GlobalOut, "InputError");
#endif
      Error("Input file contains no clauses or formulas", OTHER_ERROR);
   }
   *ax_no = parsed_ax_no;

   // /* TODO: Remove this! */
   // if (in && ScannerQuerySupportHO(in))
   // {
   //    TBPrintBankInOrder(stderr, proofstate->terms);
   // }

   return proofstate;
}


/*-----------------------------------------------------------------------
//
// Function: print_info()
//
//   Check if pid and version should be printed, if yes, do so.
//
// Global Variables: print_pid, print_version
//
// Side Effects    : Output
//
/----------------------------------------------------------------------*/

static void print_info(void)
{
   if(print_pid)
   {
      fprintf(GlobalOut, "# Pid: %lld\n", (long long)pid);
      fflush(GlobalOut);
   }
   if(print_version)
   {
      fprintf(GlobalOut, "# Version: " VERSION "\n");
      fflush(GlobalOut);
   }
}

/*-----------------------------------------------------------------------
//
// Function: print_proof_stats()
//
//   Print some statistics about the proof search. This is a pure
//   service function to make main() smaller.
//
// Global Variables: OutputLevel,
//                   print_statistics
//                   GlobalOut,
//                   ClauseClauseSubsumptionCalls,
//                   ClauseClauseSubsumptionCallsRec,
//                   ClauseClauseSubsumptionSuccesses,
//                   UnitClauseClauseSubsumptionCalls,
//                   RewriteUnboundVarFails,
//                   BWRWMatchAttempts,
//                   BWRWMatchSuccesses,
//                   CondensationAttempts,
//                   CondensationSuccesses,
//                   (possibly) UnifAttempts,
//                   (possibly) UnifSuccesses,
//                   (possibly) PDTNodeCounter
//                   (possibly) MguTimer);
//                   (possibly) SatTimer);
//                   (possibly) ParamodTimer);
//                   (possibly) PMIndexTimer);
//                   (possibly) IndexUnifTimer)
//                   (possibly) BWRWTimer);
//                   (possibly) BWRWIndexTimer)
//                   (possibly) IndexMatchTimer
//                   (possibly) FreqVecTimer);
//                   (possibly) FVIndexTimer);
//                   (possibly) SubsumeTimer);
//                   (possibly) SetSubsumeTimer
//
// Side Effects    : Output of collected statistics.
//
/----------------------------------------------------------------------*/

static void print_proof_stats(ProofState_p proofstate,
                              long parsed_ax_no,
                              long relevancy_pruned,
                              long raw_clause_no,
                              long preproc_removed)

{
   if(OutputLevel||print_statistics)
   {
      fprintf(GlobalOut, "# Parsed axioms                        : %ld\n",
              parsed_ax_no);
      fprintf(GlobalOut, "# Removed by relevancy pruning/SinE    : %ld\n",
              relevancy_pruned);
      fprintf(GlobalOut, "# Initial clauses                      : %ld\n",
              raw_clause_no);
      fprintf(GlobalOut, "# Removed in clause preprocessing      : %ld\n",
              preproc_removed);
      ProofStateStatisticsPrint(GlobalOut, proofstate);
      fprintf(GlobalOut, "# Clause-clause subsumption calls (NU) : %ld\n",
              ClauseClauseSubsumptionCalls);
      fprintf(GlobalOut, "# Rec. Clause-clause subsumption calls : %ld\n",
              ClauseClauseSubsumptionCallsRec);
      fprintf(GlobalOut, "# Non-unit clause-clause subsumptions  : %ld\n",
              ClauseClauseSubsumptionSuccesses);
      fprintf(GlobalOut, "# Unit Clause-clause subsumption calls : %ld\n",
              UnitClauseClauseSubsumptionCalls);
      fprintf(GlobalOut, "# Rewrite failures with RHS unbound    : %ld\n",
              RewriteUnboundVarFails);
      fprintf(GlobalOut, "# BW rewrite match attempts            : %ld\n",
              BWRWMatchAttempts);
      fprintf(GlobalOut, "# BW rewrite match successes           : %ld\n",
              BWRWMatchSuccesses);
      fprintf(GlobalOut, "# Condensation attempts                : %ld\n",
              CondensationAttempts);
      fprintf(GlobalOut, "# Condensation successes               : %ld\n",
              CondensationSuccesses);

#ifdef MEASURE_UNIFICATION
      fprintf(GlobalOut, "# Unification attempts                 : %ld\n",
              UnifAttempts);
      fprintf(GlobalOut, "# Unification successes                : %ld\n",
              UnifSuccesses);
#endif
#ifdef PDT_COUNT_NODES
      fprintf(GlobalOut, "# PDT nodes visited                    : %ld\n",
              PDTNodeCounter);
#endif
      fprintf(GlobalOut, "# Termbank termtop insertions          : %lld\n",
              proofstate->terms->insertions);
      PERF_CTR_PRINT(GlobalOut, MguTimer);
      PERF_CTR_PRINT(GlobalOut, SatTimer);
      PERF_CTR_PRINT(GlobalOut, ParamodTimer);
      PERF_CTR_PRINT(GlobalOut, PMIndexTimer);
      PERF_CTR_PRINT(GlobalOut, IndexUnifTimer);
      PERF_CTR_PRINT(GlobalOut, BWRWTimer);
      PERF_CTR_PRINT(GlobalOut, BWRWIndexTimer);
      PERF_CTR_PRINT(GlobalOut, IndexMatchTimer);
      PERF_CTR_PRINT(GlobalOut, FreqVecTimer);
      PERF_CTR_PRINT(GlobalOut, FVIndexTimer);
      PERF_CTR_PRINT(GlobalOut, SubsumeTimer);
      PERF_CTR_PRINT(GlobalOut, SetSubsumeTimer);
      PERF_CTR_PRINT(GlobalOut, ClauseEvalTimer);

#ifdef PRINT_INDEX_STATS
      fprintf(GlobalOut, "# Backwards rewriting index : ");
      FPIndexDistribDataPrint(GlobalOut, proofstate->gindices.bw_rw_index);
      fprintf(GlobalOut, "\n");
      /*FPIndexPrintDot(GlobalOut, "rw_bw_index",
        proofstate->gindices.bw_rw_index,
        SubtermTreePrintDot,
        proofstate->signature);*/
      fprintf(GlobalOut, "# Paramod-from index        : ");
      FPIndexDistribDataPrint(GlobalOut, proofstate->gindices.pm_from_index);
      fprintf(GlobalOut, "\n");
      FPIndexPrintDot(GlobalOut, "pm_from_index",
                      proofstate->gindices.pm_from_index,
                      SubtermTreePrintDot,
                      proofstate->signature);
      fprintf(GlobalOut, "# Paramod-into index        : ");
      FPIndexDistribDataPrint(GlobalOut, proofstate->gindices.pm_into_index);
      fprintf(GlobalOut, "\n");
      fprintf(GlobalOut, "# Paramod-neg-atom index    : ");
      FPIndexDistribDataPrint(GlobalOut, proofstate->gindices.pm_negp_index);
      fprintf(GlobalOut, "\n");
#endif
      // PDTreePrint(GlobalOut, proofstate->processed_pos_rules->demod_index);
   }
}


/*-----------------------------------------------------------------------
//
// Function: main()
//
//   Main entry point of the prover.
//
// Global Variables: Plenty, mostly flags shared with
//                   process_options. See list above.
//
// Side Effects    : Yes ;-)
//
/----------------------------------------------------------------------*/


int main(int argc, char* argv[])
{
   int              retval = NO_ERROR;
   CLState_p        state;
   ProofState_p     proofstate;
   ProofControl_p   proofcontrol;
   Clause_p         success = NULL,
      filter_success;
   bool             out_of_clauses;
   char             *finals_state = "exists",
      *sat_status = "Derivation";
   long             cnf_size = 0,
      raw_clause_no,
      preproc_removed=0,
      neg_conjectures,
      parsed_ax_no,
      relevancy_pruned = 0;
   double           preproc_time;

   assert(argv[0]);

#ifdef STACK_SIZE
   INCREASE_STACK_SIZE;
#endif

   pid = getpid();
   InitIO(NAME);

   ESignalSetup(SIGXCPU);

   h_parms = HeuristicParmsAlloc();
   fvi_parms = FVIndexParmsAlloc();
   wfcb_definitions = PStackAlloc();
   hcb_definitions = PStackAlloc();

   state = process_options(argc, argv);

   OpenGlobalOut(outname);
   print_info();


   if(state->argc ==  0)
   {
      CLStateInsertArg(state, "-");
   }

   proofstate = parse_spec(state, parse_format,
                           error_on_empty, free_symb_prop,
                           &parsed_ax_no);

   relevancy_pruned += ProofStateSinE(proofstate, sine);


   relevancy_pruned += ProofStatePreprocess(proofstate, relevance_prune_level);

   if(strategy_scheduling)
   {
      ExecuteSchedule(StratSchedule, h_parms, print_rusage);
   }

   FormulaSetDocInital(GlobalOut, OutputLevel, proofstate->f_axioms);
   ClauseSetDocInital(GlobalOut, OutputLevel, proofstate->axioms);

   if(prune_only)
   {
      fprintf(GlobalOut, "\n# Pruning successful!\n");
      TSTPOUT(GlobalOut, "Unknown");
      //goto cleanup1;
   }

   if(relevancy_pruned || incomplete)
   {
      proofstate->state_is_complete = false;
   }
   if(BuildProofObject)
   {
      FormulaSetArchive(proofstate->f_axioms, proofstate->f_ax_archive);
   }
   if((neg_conjectures =
       FormulaSetPreprocConjectures(proofstate->f_axioms,
                                    proofstate->f_ax_archive,
                                    answer_limit>0,
                                    conjectures_are_questions)))
   {
      VERBOUT("Negated conjectures.\n");
   }

   fprintf(stderr, "Before CNF!\n");
   TBPrintBankInOrder(stderr, proofstate->terms);

   fprintf(stderr, "Printing done!\n");
   //return -1;

   if(new_cnf)
   {
      cnf_size = FormulaSetCNF2(proofstate->f_axioms,
                                proofstate->f_ax_archive,
                                proofstate->axioms,
                                proofstate->terms,
                                proofstate->freshvars,
                                proofstate->gc_terms,
                                miniscope_limit);
   }
   else
   {
      cnf_size = FormulaSetCNF(proofstate->f_axioms,
                               proofstate->f_ax_archive,
                               proofstate->axioms,
                               proofstate->terms,
                               proofstate->freshvars,
                               proofstate->gc_terms);
   }


   if(cnf_size)
   {
      VERBOUT("CNFization done\n");
   }

   fprintf(stderr, "After CNF!\n");
   TBPrintBankInOrder(stderr, proofstate->terms);

   raw_clause_no = proofstate->axioms->members;
   if(!no_preproc)
   {
      if(BuildProofObject)
      {
         ClauseSetArchive(proofstate->ax_archive, proofstate->axioms);
         if(proofstate->watchlist)
         {
            ClauseSetArchive(proofstate->ax_archive, proofstate->watchlist);
         }
      }
      preproc_removed = ClauseSetPreprocess(proofstate->axioms,
                                            proofstate->watchlist,
                                            proofstate->archive,
                                            proofstate->tmp_terms,
                                            eqdef_incrlimit,
                                            eqdef_maxclauses);

      fprintf(stderr, "preproc removed : %d\n", preproc_removed);
   }

   proofcontrol = ProofControlAlloc();
   ProofControlInit(proofstate, proofcontrol, h_parms,
                    fvi_parms, wfcb_definitions, hcb_definitions);
   PCLFullTerms = pcl_full_terms; /* Preprocessing always uses full
                                     terms, so we set the flag for
                                     the main proof search only now! */
   GlobalIndicesInit(&(proofstate->wlindices),
                     proofstate->signature,
                     proofcontrol->heuristic_parms.rw_bw_index_type,
                     "NoIndex",
                     "NoIndex");
   ProofStateInit(proofstate, proofcontrol);
   ProofStateInitWatchlist(proofstate, proofcontrol->ocb,
                           watchlist_filename, parse_format);

   VERBOUT2("Prover state initialized\n");


   fprintf(stderr, "Clauses: \n");
   ClauseSetPrint(stderr, proofstate->axioms, true);

   for(Clause_p cl = proofstate->axioms->anchor; cl != proofstate->axioms->anchor; cl = cl->succ)
   {
     cl->date = -100; // to make sure it is rewritten.
     EqnListSetProp(cl->literals, EPIsOriented);
   }

   fprintf(stderr, "Clauses printed. \n");


   /* The file is lfho.pdt.p */

   /* Assuming this state of clauses:
        Clauses: 
    1   tcf(i_0_10, plain, ![X1:$i > $i]:g($@_var(X1,a),c)=d).
    2   tcf(i_0_8, plain, ![X1:$i > $i > $i]:$@_var(X1,a,c)=f(c,d,a,b)).
    3   tcf(i_0_14, negated_conjecture, ![X1:$i > $i > $i]:$@_var(X1,a,c)=f(c,d,a,b)).
    4   tcf(i_0_12, plain, ![X3:$i > $i > $i > $i > $i, X2, X1:$i > $i > $i > $i]:$@_var(X1,a,X2,b)=$@_var(X3,b,a,c,b)).
    5   cnf(i_0_11, plain, (g(h(b,a),c)=g(f(a,a,a,a),b))).
    6   tcf(i_0_13, plain, ![X1:$i > $i > $i]:$@_var(X1,a)!=f(c,a,d)).
    7   tcf(i_0_9, plain, f(c,d,a)!=f(a,a,a)).
        Clauses printed. 
  */

   /* appliedVariable -- clause 3 -- X a c*/
   ClausePos_p appVar = ClausePosCellAlloc();
   Clause_p    appVarClause = proofstate->axioms->anchor->succ->succ->succ;
   appVar->clause  = appVarClause;
   appVar->literal = appVarClause->literals;

   /*Just a hack to try rewriting */
   EqnSetProp(appVar->literal, EPIsOriented);
   appVarClause->date = 1;

   appVar->side    = LeftSide;
   appVar->pos     = NULL;
   PDTreeInsert(proofstate->processed_pos_rules->demod_index, appVar);

   /* partially applied term -- clause 7  -- f c d a*/
   ClausePos_p partiallyApplied = ClausePosCellAlloc();
   Clause_p    partiallyAppliedClause = proofstate->axioms->anchor->succ->succ->succ->succ
                                                                  ->succ->succ->succ;
   partiallyApplied->clause  = partiallyAppliedClause;
   partiallyApplied->literal = partiallyAppliedClause->literals;

   EqnSetProp(partiallyApplied->literal, EPIsOriented);
   partiallyAppliedClause->date = 1;

   partiallyApplied->side    = LeftSide;
   partiallyApplied->pos     = NULL;
   PDTreeInsert(proofstate->processed_pos_rules->demod_index, partiallyApplied);

   /* first term to match -- clause 2, right -- f c d a b*/
   Term_p firstToMatch = proofstate->axioms->anchor->succ->succ->literals->rterm;

   PDTreeSearchInit(proofstate->processed_pos_rules->demod_index, firstToMatch, SysDateInvalidTime(), true);
   Subst_p subst = SubstAlloc();
   MatchInfo_p mi = PDTreeFindNextDemodulator(proofstate->processed_pos_rules->demod_index, subst);

   fprintf(stderr, "Matching :");
   TermPrint(stderr, firstToMatch, proofstate->terms->sig, DEREF_ALWAYS);
   fprintf(stderr, ".\n");

   Term_p matcher =  GetMatcher(mi);
   if (!matcher)
   {
      fprintf(stderr, "Nothing found (%p)!!!\n", mi);
   }
   else
   {
      fprintf(stderr, "Matcher :");
      TermPrint(stderr, matcher, proofstate->terms->sig, DEREF_ALWAYS);
      fprintf(stderr, "\nWhat is matched : ");
      TermPrint(stderr, MatchInfoMatchedPrefix(mi, proofstate->terms, firstToMatch), proofstate->terms->sig, DEREF_ALWAYS);
   }
   SubstBacktrack(subst);
   PDTreeSearchExit(proofstate->processed_pos_rules->demod_index);

   /* applied var inside -- clause 1, left -- g (X a) c*/
   ClausePos_p appVarInside = ClausePosCellAlloc();
   Clause_p    appVarInsideClause = proofstate->axioms->anchor->succ;
   appVarInside->clause  = appVarInsideClause;
   appVarInside->literal = appVarInsideClause->literals;

   EqnSetProp(appVarInside->literal, EPIsOriented);
   appVarInsideClause->date = 1;

   appVarInside->side    = LeftSide;
   appVarInside->pos     = NULL;
   PDTreeInsert(proofstate->processed_pos_rules->demod_index, appVarInside);


   //PDTreePrint(stderr, proofstate->processed_pos_rules->demod_index);
   /* second to match -- clause 5, left  -- g (h b a) c*/
   Term_p secondToMatch = proofstate->axioms->anchor->succ->succ->succ->succ->succ->literals->lterm;
   fprintf(stderr, "\nSecond to match :");
   TermPrint(stderr, secondToMatch, proofstate->terms->sig, DEREF_ALWAYS);

   PDTreeSearchInit(proofstate->processed_pos_rules->demod_index, secondToMatch, SysDateInvalidTime(), true);
   mi = PDTreeFindNextDemodulator(proofstate->processed_pos_rules->demod_index, subst);

   matcher =  GetMatcher(mi);
   if (!matcher)
   {
      fprintf(stderr, "Nothing found (%p)!!!\n", mi);
   }
   else
   {
      fprintf(stderr, "\nMatcher :");
      TermPrint(stderr, matcher, proofstate->terms->sig, DEREF_ALWAYS);
      fprintf(stderr, "\nWhat is matched : ");
      TermPrint(stderr, MatchInfoMatchedPrefix(mi, proofstate->terms, secondToMatch), proofstate->terms->sig, DEREF_ALWAYS);
   }


   SubstBacktrack(subst);
   PDTreeSearchExit(proofstate->processed_pos_rules->demod_index);


   /* Varible both applied an nonaplied in the same term -- X a Y b -- 4 left*/
   ClausePos_p appVarInOut = ClausePosCellAlloc();
   Clause_p    appVarInOutClause = proofstate->axioms->anchor->succ->succ->succ->succ;
   appVarInOut->clause  = appVarInOutClause;
   appVarInOut->literal = appVarInOutClause->literals;

   EqnSetProp(appVarInOut->literal, EPIsOriented);
   appVarInOutClause->date = 1;

   appVarInOut->side    = LeftSide;
   appVarInOut->pos     = NULL;
   PDTreeInsert(proofstate->processed_pos_rules->demod_index, appVarInOut);

   fprintf(stderr, "\nCurrently in the PDT: \n");
   PDTreePrint(stderr, proofstate->processed_pos_rules->demod_index);


   Term_p thirdToMatch = proofstate->axioms->anchor->succ->succ->succ->succ->literals->rterm;
   fprintf(stderr, "\nThird to match :");
   /* X(b,a,c,b) -- 4 -- right*/
   TermPrint(stderr, thirdToMatch, proofstate->terms->sig, DEREF_ALWAYS);

   PDTreeSearchInit(proofstate->processed_pos_rules->demod_index, thirdToMatch, SysDateInvalidTime(), true);
   mi = PDTreeFindNextDemodulator(proofstate->processed_pos_rules->demod_index, subst);

   matcher =  GetMatcher(mi);
   if (!matcher)
   {
      fprintf(stderr, "\nNothing found (%p)!!!\n", mi);
   }
   else
   {
      fprintf(stderr, "\nMatcher :");
      TermPrint(stderr, matcher, proofstate->terms->sig, DEREF_NEVER);
      fprintf(stderr, "\nWhat is matched : ");
      TermPrint(stderr, MatchInfoMatchedPrefix(mi, proofstate->terms, thirdToMatch), proofstate->terms->sig, DEREF_ALWAYS);
   }


   SubstBacktrack(subst);
   PDTreeSearchExit(proofstate->processed_pos_rules->demod_index);


   /* Idea is that this variable matches up to some point -- X a -> 
      has to match f c d a b .. X matches f c d and a matches a..
      so it is matched up to some point */
   ClausePos_p appVarPar = ClausePosCellAlloc();
   Clause_p    appVarParClause = proofstate->axioms->anchor->succ->succ->succ
                                                           ->succ->succ->succ;
   appVarPar->clause  = appVarParClause;
   appVarPar->literal = appVarParClause->literals;

   EqnSetProp(appVarPar->literal, EPIsOriented);
   appVarParClause->date = 1;


   appVarPar->side    = LeftSide;
   appVarPar->pos     = NULL;
   PDTreeInsert(proofstate->processed_pos_rules->demod_index, appVarPar);
   

   fprintf(stderr, "\nFourth to match :");
   /* X(b,a,c,b) -- 5 -- right*/
   TermPrint(stderr, firstToMatch, proofstate->terms->sig, DEREF_ALWAYS);
   PDTreeSearchInit(proofstate->processed_pos_rules->demod_index, firstToMatch, SysDateInvalidTime(), true);

   mi = PDTreeFindNextDemodulator(proofstate->processed_pos_rules->demod_index, subst);

   matcher =  GetMatcher(mi);
   if (!matcher)
   {
      fprintf(stderr, "\nNothing found (%p)!!!\n", mi);
   }
   else
   {
      fprintf(stderr, "\nMatcher :");
      TermPrint(stderr, matcher, proofstate->terms->sig, DEREF_ALWAYS);
      fprintf(stderr, "\nWhat is matched : ");
      TermPrint(stderr, MatchInfoMatchedPrefix(mi, proofstate->terms, firstToMatch), proofstate->terms->sig, DEREF_ALWAYS);
   }

   fprintf(stderr, "\nCurrently in the PDT: \n");
   PDTreePrint(stderr, proofstate->processed_pos_rules->demod_index);

   SubstBacktrack(subst);
   PDTreeSearchExit(proofstate->processed_pos_rules->demod_index);



   return retval;
}


/*-----------------------------------------------------------------------
//
// Function: check_fp_index_arg()
//
//   Check in arg is a valid term describing a FP-index function. If
//   yes, return true. If no, print error (nominally return false).
//
// Global Variables: -
//
// Side Effects    : May terminate program with error.
//
/----------------------------------------------------------------------*/

bool check_fp_index_arg(char* arg, char* opt)
{
   DStr_p err;

   if(GetFPIndexFunction(arg)||(strcmp(arg, "NoIndex")==0))
   {
      return true;
   }
   err = DStrAlloc();
   DStrAppendStr(err,
                 "Wrong argument to option ");
   DStrAppendStr(err,
                 opt);
   DStrAppendStr(err,
                 ". Possible values: ");
   DStrAppendStrArray(err, FPIndexNames, ", ");
   Error(DStrView(err), USAGE_ERROR);
   DStrFree(err);

   return false;
}


/*-----------------------------------------------------------------------
//
// Function: process_options()
//
//   Read and process the command line option, return (the pointer to)
//   a CLState object containing the remaining arguments.
//
// Global Variables: opts, Verbose, TBPrintInternalInfo
//
// Side Effects    : Sets variables, may terminate with program
//                   description if option -h or --help was present
//
/----------------------------------------------------------------------*/

CLState_p process_options(int argc, char* argv[])
{
   Opt_p handle;
   CLState_p state;
   char*  arg;
   long   tmp;
   rlim_t mem_limit;

   state = CLStateAlloc(argc,argv);

   while((handle = CLStateGetOpt(state, &arg, opts)))
   {
      switch(handle->option_code)
      {
      case OPT_VERBOSE:
            Verbose = CLStateGetIntArg(handle, arg);
            break;
      case OPT_HELP:
            print_help(stdout);
            exit(NO_ERROR);
      case OPT_VERSION:
            fprintf(stdout, "E " VERSION " " E_NICKNAME "\n");
            exit(NO_ERROR);
      case OPT_OUTPUT:
            outname = arg;
            break;
      case OPT_SILENT:
            OutputLevel = 0;
            break;
      case OPT_OUTPUTLEVEL:
            OutputLevel = CLStateGetIntArg(handle, arg);
            break;
      case OPT_PROOF_OBJECT:
            BuildProofObject = MAX(CLStateGetIntArgCheckRange(handle, arg, 0, 3),
                                   BuildProofObject);
            print_derivation = POList;
            break;
      case OPT_PROOF_GRAPH:
            BuildProofObject = MAX(1, BuildProofObject);
            print_derivation = CLStateGetIntArg(handle, arg)+1;
            break;
      case OPT_FULL_DERIV:
            print_full_deriv = true;
            break;
      case OPT_FORCE_DERIV:
            force_deriv_output = CLStateGetIntArgCheckRange(handle, arg, 0, 2);
            BuildProofObject = MAX(1, BuildProofObject);
            break;
      case OPT_RECORD_GIVEN_CLAUSES:
            BuildProofObject = MAX(1, BuildProofObject);
            ProofObjectRecordsGCSelection = true;
            break;
      case OPT_TRAINING:
            BuildProofObject = MAX(1, BuildProofObject);
            ProofObjectRecordsGCSelection = true;
            proc_training_data = CLStateGetIntArg(handle, arg);
            break;
      case OPT_PCL_COMPRESSED:
            pcl_full_terms = false;
            break;
      case OPT_PCL_COMPACT:
            PCLStepCompact = true;
            break;
      case OPT_PCL_SHELL_LEVEL:
            PCLShellLevel =  CLStateGetIntArgCheckRange(handle, arg, 0, 2);
            break;
      case OPT_PRINT_STATISTICS:
            print_statistics = true;
            break;
      case OPT_EXPENSIVE_DETAILS:
            TBPrintDetails = true;
            break;
      case OPT_PRINT_SATURATED:
            outdesc = arg;
            CheckOptionLetterString(outdesc, "teigEIGaA", "-S (--print-saturated)");
            print_sat = true;
            break;
      case OPT_PRINT_SAT_INFO:
            outinfo = true;
            break;
      case OPT_FILTER_SATURATED:
            filterdesc = arg;
            CheckOptionLetterString(filterdesc, "eigEIGaA", "--filter-saturated");
            filter_sat = true;
            break;
      case OPT_PRUNE_ONLY:
            OutputLevel = 4;
            prune_only   = true;
            break;
      case OPT_CNF_ONLY:
            outdesc    = "teigEIG";
            print_sat  = true;
            proc_limit = 0;
            cnf_only   = true;
            break;
      case OPT_PRINT_PID:
            print_pid = true;
            break;
      case OPT_PRINT_VERSION:
            print_version = true;
            break;
      case OPT_REQUIRE_NONEMPTY:
            error_on_empty = true;
            break;
      case OPT_MEM_LIMIT:
            if(strcmp(arg, "Auto")==0)
            {
               long long tmpmem = GetSystemPhysMemory();

               if(tmpmem==-1)
               {
                  Error("Cannot find physical memory automatically. "
                        "Give explicit value to --memory-limit", OTHER_ERROR);
               }
               VERBOSE(fprintf(stderr,
                               "Physical memory determined as %lld MB\n",
                               tmpmem););

               mem_limit = 0.8*tmpmem;

               h_parms->delete_bad_limit =
                  (float)(mem_limit-2)*0.7*MEGA;
            }
            else
            {
               /* We expect the user to know what he is doing */
               mem_limit = CLStateGetIntArg(handle, arg);
            }
            VERBOSE(fprintf(stderr,
                            "Memory limit set to %lld MB\n",
                            (long long)mem_limit););
            h_parms->mem_limit = MEGA*mem_limit;
            break;
      case OPT_CPU_LIMIT:
            HardTimeLimit = CLStateGetIntArg(handle, arg);
            ScheduleTimeLimit = HardTimeLimit;
            if((SoftTimeLimit != RLIM_INFINITY) &&
               (HardTimeLimit<=SoftTimeLimit))
            {
               Error("Hard time limit has to be larger than soft"
                     "time limit", USAGE_ERROR);
            }
            break;
      case OPT_SOFTCPU_LIMIT:
            SoftTimeLimit = CLStateGetIntArg(handle, arg);
            ScheduleTimeLimit = SoftTimeLimit;

            if((HardTimeLimit != RLIM_INFINITY) &&
               (HardTimeLimit<=SoftTimeLimit))
            {
               Error("Soft time limit has to be smaller than hard"
                     "time limit", USAGE_ERROR);
            }
            break;
      case OPT_RUSAGE_INFO:
            print_rusage = true;
            break;
      case OPT_STEP_LIMIT:
            step_limit = CLStateGetIntArg(handle, arg);
            break;
      case OPT_ANSWER_LIMIT:
            answer_limit = CLStateGetIntArg(handle, arg);
            break;
      case OPT_CONJ_ARE_QUEST:
            conjectures_are_questions = true;
            break;
      case OPT_PROC_LIMIT:
            proc_limit = CLStateGetIntArg(handle, arg);
            break;
      case OPT_UNPROC_LIMIT:
            unproc_limit = CLStateGetIntArg(handle, arg);
            break;
      case OPT_TOTAL_LIMIT:
            total_limit = CLStateGetIntArg(handle, arg);
            break;
      case OPT_GENERATED_LIMIT:
            generated_limit = CLStateGetIntArg(handle, arg);
            break;
      case OPT_TB_INSERT_LIMIT:
            tb_insert_limit = CLStateGetIntArg(handle, arg);
            break;
      case OPT_NO_INFIX:
            EqnUseInfix = false;
            break;
      case OPT_FULL_EQ_REP:
            EqnFullEquationalRep = true;
            break;
      case OPT_LOP_PARSE:
            parse_format = LOPFormat;
            break;
      case OPT_PCL_PRINT:
            DocOutputFormat = pcl_format;
            break;
      case OPT_TPTP_PRINT:
            OutputFormat = TPTPFormat;
            EqnFullEquationalRep = false;
            EqnUseInfix = false;
            break;
      case OPT_TPTP_FORMAT:
            parse_format = TPTPFormat;
            OutputFormat = TPTPFormat;
            EqnFullEquationalRep = false;
            EqnUseInfix = false;
            break;
      case OPT_TSTP_PARSE:
            parse_format = TSTPFormat;
            break;
      case OPT_TSTP_PRINT:
            DocOutputFormat = tstp_format;
            OutputFormat = TSTPFormat;
            EqnUseInfix = true;
            break;
      case OPT_TSTP_FORMAT:
            parse_format = TSTPFormat;
            DocOutputFormat = tstp_format;
            OutputFormat = TSTPFormat;
            EqnUseInfix = true;
            break;
      case OPT_AUTO:
            h_parms->heuristic_name = "Auto";
            h_parms->ordertype = AUTO;
            sine = "Auto";
            break;
      case OPT_SATAUTO:
            h_parms->heuristic_name = "Auto";
            h_parms->ordertype = AUTO;
            break;
      case OPT_AUTODEV:
            h_parms->heuristic_name = "AutoDev";
            h_parms->ordertype = AUTODEV;
            sine = "Auto";
            break;
      case OPT_SATAUTODEV:
            h_parms->heuristic_name = "AutoDev";
            h_parms->ordertype = AUTODEV;
            break;
      case OPT_AUTO_SCHED:
            strategy_scheduling = true;
            sine = "Auto";
            break;
      case OPT_SATAUTO_SCHED:
            strategy_scheduling = true;
            break;
      case OPT_NO_PREPROCESSING:
            no_preproc = true;
            break;
      case OPT_EQ_UNFOLD_LIMIT:
            eqdef_incrlimit = CLStateGetIntArg(handle, arg);
            break;
      case OPT_EQ_UNFOLD_MAXCLAUSES:
            eqdef_maxclauses = CLStateGetIntArg(handle, arg);
            break;
      case OPT_NO_EQ_UNFOLD:
            eqdef_incrlimit = INT_MIN;
            break;
      case OPT_SINE:
            sine = arg;
            break;
      case OPT_REL_PRUNE_LEVEL:
            relevance_prune_level = CLStateGetIntArg(handle, arg);
            break;
      case OPT_PRESAT_SIMPLIY:
            h_parms->presat_interreduction = true;
            break;
      case OPT_AC_HANDLING:
            if(strcmp(arg, "None")==0)
            {
               h_parms->ac_handling = NoACHandling;
            }
            else if(strcmp(arg, "DiscardAll")==0)
            {
               h_parms->ac_handling = ACDiscardAll;
            }
            else if(strcmp(arg, "KeepUnits")==0)
            {
               h_parms->ac_handling = ACKeepUnits;
            }
            else if(strcmp(arg, "KeepOrientable")==0)
            {
               h_parms->ac_handling = ACKeepOrientable;
            }
            else
            {
               Error("Option --ac_handling requires None, DiscardAll, "
                     "KeepUnits, or KeepOrientable as an argument",
                     USAGE_ERROR);
            }
            break;
      case OPT_AC_ON_PROC:
            h_parms->ac_res_aggressive = false;
            break;
      case OPT_NO_GENERATION:
            h_parms->selection_strategy=SelectNoGeneration;
            break;
      case OPT_SELECT_ON_PROC_ONLY:
            h_parms->select_on_proc_only = true;
            break;
      case OPT_INHERIT_PM_LIT:
            h_parms->inherit_paramod_lit = true;
            break;
      case OPT_INHERIT_GOAL_PM_LIT:
            h_parms->inherit_goal_pm_lit = true;
            break;
      case OPT_INHERIT_CONJ_PM_LIT:
            h_parms->inherit_conj_pm_lit = true;
            break;

      case OPT_LITERAL_SELECT:
            h_parms->selection_strategy = GetLitSelFun(arg);
            if(!h_parms->selection_strategy)
            {
               DStr_p err = DStrAlloc();
               DStrAppendStr(err,
                             "Wrong argument to option -W "
                             "(--literal-selection-strategy). Possible "
                             "values: ");
               LitSelAppendNames(err);
               Error(DStrView(err), USAGE_ERROR);
               DStrFree(err);
            }
            if(h_parms->selection_strategy == SelectNoGeneration)
            {
               inf_sys_complete = false;
            }
            break;
      case OPT_POS_LITSEL_MIN:
            h_parms->pos_lit_sel_min = CLStateGetIntArg(handle, arg);
            break;
      case OPT_POS_LITSEL_MAX:
            h_parms->pos_lit_sel_max = CLStateGetIntArg(handle, arg);
            break;
      case OPT_NEG_LITSEL_MIN:
            h_parms->neg_lit_sel_min = CLStateGetIntArg(handle, arg);
            break;
      case OPT_NEG_LITSEL_MAX:
            h_parms->neg_lit_sel_max = CLStateGetIntArg(handle, arg);
            break;
      case OPT_ALL_LITSEL_MIN:
            h_parms->all_lit_sel_min = CLStateGetIntArg(handle, arg);
            break;
      case OPT_ALL_LITSEL_MAX:
            h_parms->all_lit_sel_max = CLStateGetIntArg(handle, arg);
            break;
      case OPT_WEIGHT_LITSEL_MIN:
            h_parms->weight_sel_min = CLStateGetIntArg(handle, arg);
            break;
      case OPT_PREFER_INITIAL_CLAUSES:
            h_parms->prefer_initial_clauses = true;
            break;
      case OPT_HEURISTIC:
            h_parms->heuristic_name = arg;
            break;
      case OPT_FILTER_LIMIT:
            h_parms->filter_limit = CLStateGetIntArg(handle, arg);
            break;
      case OPT_FILTER_COPIES_LIMIT:
            h_parms->filter_copies_limit = CLStateGetIntArg(handle, arg);
            break;
      case OPT_DELETE_BAD_LIMIT:
            h_parms->delete_bad_limit = CLStateGetIntArg(handle, arg);
            break;
      case OPT_ASSUME_COMPLETENESS:
            assume_inf_sys_complete = true;
            break;
      case OPT_ASSUME_INCOMPLETENESS:
            incomplete = true;
            break;
      case OPT_NO_GC_FORWARD_SIMPL:
            h_parms->enable_given_forward_simpl = false;
            break;
      case OPT_DISABLE_EQ_FACTORING:
            h_parms->enable_eq_factoring = false;
            inf_sys_complete = false;
            break;
      case OPT_DISABLE_NEGUNIT_PM:
            h_parms->enable_neg_unit_paramod = false;
            inf_sys_complete = false;
            break;
      case OPT_CONDENSING:
            h_parms->condensing = true;
            break;
      case OPT_CONDENSING_AGGRESSIVE:
            h_parms->condensing = true;
            h_parms->condensing_aggressive = true;
            break;
      case OPT_USE_SIM_PARAMOD:
            h_parms->pm_type = ParamodAlwaysSim;
            break;
      case OPT_USE_ORIENTED_SIM_PARAMOD:
            h_parms->pm_type = ParamodOrientedSim;
            break;
      case OPT_SPLIT_TYPES:
            h_parms->split_clauses = CLStateGetIntArg(handle, arg);
            break;
      case OPT_SPLIT_HOW:
            h_parms->split_method = CLStateGetIntArgCheckRange(handle, arg, 0, 2);
            break;
      case OPT_SPLIT_AGGRESSIVE:
            h_parms->split_aggressive = true;
            break;
      case OPT_SPLIT_REUSE_DEFS:
            h_parms->split_fresh_defs = false;
            break;
      case OPT_REWEIGHT_LIMIT:
            h_parms->reweight_limit = CLStateGetIntArg(handle, arg);
            break;
      case OPT_ORDERING:
            if(strcmp(arg, "Auto")==0)
            {
               h_parms->ordertype = AUTO;
            }
            else if(strcmp(arg, "AutoCASC")==0)
            {
               h_parms->ordertype = AUTOCASC;
            }
            else if(strcmp(arg, "AutoDev")==0)
            {
               h_parms->ordertype = AUTODEV;
            }
            else if(strcmp(arg, "AutoSched0")==0)
            {
               h_parms->ordertype = AUTOSCHED0;
            }
            else if(strcmp(arg, "AutoSched1")==0)
            {
               h_parms->ordertype = AUTOSCHED1;
            }
            else if(strcmp(arg, "AutoSched2")==0)
            {
               h_parms->ordertype = AUTOSCHED2;
            }
            else if(strcmp(arg, "AutoSched3")==0)
            {
               h_parms->ordertype = AUTOSCHED3;
            }
            else if(strcmp(arg, "AutoSched4")==0)
            {
               h_parms->ordertype = AUTOSCHED4;
            }
            else if(strcmp(arg, "AutoSched5")==0)
            {
               h_parms->ordertype = AUTOSCHED5;
            }
            else if(strcmp(arg, "AutoSched6")==0)
            {
               h_parms->ordertype = AUTOSCHED6;
            }
            else if(strcmp(arg, "AutoSched7")==0)
            {
               h_parms->ordertype = AUTOSCHED7;
            }
            else if(strcmp(arg, "Optimize")==0)
            {
               h_parms->ordertype = OPTIMIZE_AX;
            }
            else if(strcmp(arg, "LPO")==0)
            {
               h_parms->ordertype = LPO;
            }
            else if(strcmp(arg, "LPOCopy")==0)
            {
               h_parms->ordertype = LPOCopy;
            }
            else if(strcmp(arg, "LPO4")==0)
            {
               h_parms->ordertype = LPO4;
            }
            else if(strcmp(arg, "LPO4Copy")==0)
            {
               h_parms->ordertype = LPO4Copy;
            }
            else if(strcmp(arg, "KBO")==0)
            {
               h_parms->ordertype = KBO;
            }
            else if(strcmp(arg, "KBO6")==0)
            {
               h_parms->ordertype = KBO6;
            }
            else
            {
               Error("Option -t (--term-ordering) requires Auto, "
                     "AutoCASC, AutoDev, AutoSched0, AutoSched1, "
                     "AutoSched2, AutoSched3, AutoSched4, AutoSched5,"
                     "AutoSched6, AutoSched7, Optimize, "
                     "LPO, LPO4, KBO or KBO6 as an argument",
                     USAGE_ERROR);
            }
            break;
      case OPT_TO_WEIGHTGEN:
            h_parms->to_weight_gen = TOTranslateWeightGenMethod(arg);
            if(!h_parms->to_weight_gen)
            {
               DStr_p err = DStrAlloc();
               DStrAppendStr(err,
                             "Wrong argument to option -w "
                             "(--order-weight-generation). Possible "
                             "values: ");
               DStrAppendStrArray(err, TOWeightGenNames, ", ");
               Error(DStrView(err), USAGE_ERROR);
               DStrFree(err);
            }
            break;
      case OPT_TO_WEIGHTS:
            h_parms->to_pre_weights = arg;
            break;
      case OPT_TO_PRECGEN:
            h_parms->to_prec_gen = TOTranslatePrecGenMethod(arg);
            if(!h_parms->to_prec_gen)
            {
               DStr_p err = DStrAlloc();
               DStrAppendStr(err,
                             "Wrong argument to option -G "
                             "(--order-precedence-generation). Possible "
                             "values: ");
               DStrAppendStrArray(err, TOPrecGenNames, ", ");
               Error(DStrView(err), USAGE_ERROR);
               DStrFree(err);
            }
            break;
      case OPT_TO_CONSTWEIGHT:
            h_parms->to_const_weight = CLStateGetIntArg(handle, arg);
            if(h_parms->to_const_weight<=0)
            {
               Error("Argument to option -c (--order-constant-weight) "
                     "has to be > 0", USAGE_ERROR);
            }
            break;
      case OPT_TO_PRECEDENCE:
            h_parms->to_pre_prec = arg;
            break;
      case OPT_TO_LPO_RECLIMIT:
            LPORecursionDepthLimit = CLStateGetIntArg(handle, arg);
            if(LPORecursionDepthLimit<=0)
            {
               Error("Argument to option --lpo-recursion-limit "
                     "has to be > 0", USAGE_ERROR);
            }
            if(LPORecursionDepthLimit>20000)
            {
               Warning("Using very large values for "
                       "--lpo-recursion-limit may lead to stack "
                       "overflows and segmentation faults.");
            }
      case OPT_TO_RESTRICT_LIT_CMPS:
            h_parms->no_lit_cmp = true;
            break;
      case OPT_TPTP_SOS:
            h_parms->use_tptp_sos = true;
            break;
      case OPT_ER_DESTRUCTIVE:
            h_parms->er_varlit_destructive = true;
            break;
      case OPT_ER_STRONG_DESTRUCTIVE:
            h_parms->er_varlit_destructive = true; /* Implied */
            h_parms->er_strong_destructive = true;
            break;
      case OPT_ER_AGGRESSIVE:
            h_parms->er_aggressive = true;
            break;
      case OPT_FORWARD_CSR:
            h_parms->forward_context_sr = true;
            break;
      case OPT_FORWARD_CSR_AGGRESSIVE:
            h_parms->forward_context_sr = true;
            h_parms->forward_context_sr_aggressive = true;
            break;
      case OPT_BACKWARD_CSR:
            h_parms->backward_context_sr = true;
            break;
      case OPT_RULES_GENERAL:
            h_parms->prefer_general = true;
            break;
      case OPT_FORWARD_DEMOD:
            h_parms->forward_demod = CLStateGetIntArgCheckRange(handle, arg, 0, 2);
            break;
      case OPT_STRONG_RHS_INSTANCE:
            RewriteStrongRHSInst = true;
            break;
      case OPT_STRONGSUBSUMPTION:
            StrongUnitForwardSubsumption = true;
            break;
      case OPT_WATCHLIST:
            if(strcmp(WATCHLIST_INLINE_STRING, arg)==0 ||
               strcmp(WATCHLIST_INLINE_QSTRING, arg)==0  )
            {
               watchlist_filename = UseInlinedWatchList;
            }
            else
            {
               watchlist_filename = arg;
            }
            break;
      case OPT_WATCHLIST_NO_SIMPLIFY:
            h_parms->watchlist_simplify = false;
            break;
      case OPT_NO_INDEXED_SUBSUMPTION:
            fvi_parms->cspec.features = FVINoFeatures;
            break;
      case OPT_FVINDEX_STYLE:
            if(strcmp(arg, "None")==0)
            {
               fvi_parms->cspec.features = FVINoFeatures;
            }
            else if(strcmp(arg, "Direct")==0)
            {
               fvi_parms->use_perm_vectors = false;
            }
            else if(strcmp(arg, "Perm")==0)
            {
               fvi_parms->use_perm_vectors = true;
               fvi_parms->eliminate_uninformative = false;
            }
            else if(strcmp(arg, "PermOpt")==0)
            {
               fvi_parms->use_perm_vectors = true;
               fvi_parms->eliminate_uninformative = true;
            }
            else
            {
               Error("Option --subsumption-indexing requires "
                     "'None', 'Direct', 'Perm', or 'PermOpt'.", USAGE_ERROR);
            }
            break;
      case OPT_FVINDEX_FEATURETYPES:
            if(strcmp(arg, "None")==0)
            {
               fvi_parms->cspec.features = FVINoFeatures;
            }
            else if(strcmp(arg, "AC")==0)
            {
               fvi_parms->cspec.features = FVIACFeatures;
            }
            else if(strcmp(arg, "SS")==0)
            {
               fvi_parms->cspec.features = FVISSFeatures;
            }
            else if(strcmp(arg, "All")==0)
            {
               fvi_parms->cspec.features = FVIAllFeatures;
            }
            else if(strcmp(arg, "Bill")==0)
            {
               fvi_parms->cspec.features = FVIBillFeatures;
            }
            else if(strcmp(arg, "BillPlus")==0)
            {
               fvi_parms->cspec.features = FVIBillPlusFeatures;
            }
            else if(strcmp(arg, "ACFold")==0)
            {
               fvi_parms->cspec.features = FVIACFold;
            }
            else if(strcmp(arg, "ACStagger")==0)
            {
               fvi_parms->cspec.features = FVIACStagger;
            }
            else
            {
               Error("Option --fvindex-featuretypes requires "
                     "'None', 'AC', 'SS', or 'All'.", USAGE_ERROR);
            }
            break;
      case OPT_FVINDEX_MAXFEATURES:
            tmp = CLStateGetIntArg(handle, arg);
            if(tmp<=0)
            {
               Error("Argument to option --fvindex-maxfeatures "
                     "has to be > 0", USAGE_ERROR);
            }
            fvi_parms->max_symbols = CLStateGetIntArgCheckRange(handle, arg, 0, LONG_MAX);
            break;
      case OPT_FVINDEX_SLACK:
            fvi_parms->symbol_slack = CLStateGetIntArgCheckRange(handle, arg, 0, LONG_MAX);
            break;
      case OPT_RW_BW_INDEX:
            check_fp_index_arg(arg, "--rw-bw-index");
            strcpy(h_parms->rw_bw_index_type, arg);
            break;
      case OPT_PM_FROM_INDEX:
            check_fp_index_arg(arg, "--pm-from-index");
            strcpy(h_parms->pm_from_index_type, arg);
            break;
      case OPT_PM_INTO_INDEX:
            check_fp_index_arg(arg, "--pm-into-index");
            strcpy(h_parms->pm_into_index_type, arg);
            break;
      case OPT_FP_INDEX:
            check_fp_index_arg(arg, "--fp-index");
            strcpy(h_parms->rw_bw_index_type, arg);
            strcpy(h_parms->pm_from_index_type, arg);
            strcpy(h_parms->pm_into_index_type, arg);
            break;
      case OPT_PDT_NO_SIZECONSTR:
            PDTreeUseSizeConstraints = false;
            break;
      case OPT_PDT_NO_AGECONSTR:
            PDTreeUseAgeConstraints = false;
            break;
      case OPT_DETSORT_RW:
            h_parms->detsort_bw_rw = true;
            break;
      case OPT_DETSORT_NEW:
            h_parms->detsort_tmpset = true;
            break;
      case OPT_DEFINE_WFUN:
            PStackPushP(wfcb_definitions, arg);
            break;
      case OPT_DEFINE_HEURISTIC:
            PStackPushP(hcb_definitions, arg);
            break;
      case OPT_FREE_NUMBERS:
            free_symb_prop = free_symb_prop|FPIsInteger|FPIsRational|FPIsFloat;
            break;
      case OPT_FREE_OBJECTS:
            free_symb_prop = free_symb_prop|FPIsObject;
            break;
      case OPT_DEF_CNF_OLD:
            new_cnf = false;
            /* Intentional fall-through */
      case OPT_DEF_CNF:
            FormulaDefLimit = CLStateGetIntArgCheckRange(handle, arg, 0, LONG_MAX);
            break;
      case OPT_MINISCOPE_LIMIT:
            miniscope_limit =  CLStateGetIntArgCheckRange(handle, arg, 0, LONG_MAX);
            break;
      case OPT_PRINT_TYPES:
            TermPrintTypes = true;
            break;
      default:
            assert(false && "Unknown option");
            break;
      }
   }
   if((HardTimeLimit!=RLIM_INFINITY)||(SoftTimeLimit!=RLIM_INFINITY))
   {
      if(SoftTimeLimit!=RLIM_INFINITY)
      {
         SetSoftRlimitErr(RLIMIT_CPU, SoftTimeLimit, "RLIMIT_CPU (E-Soft)");
         TimeLimitIsSoft = true;
      }
      else
      {
         SetSoftRlimitErr(RLIMIT_CPU, HardTimeLimit, "RLIMIT_CPU (E-Hard)");
         TimeLimitIsSoft = false;
      }

      if(SetSoftRlimit(RLIMIT_CORE, 0)!=RLimSuccess)
      {
         perror("eprover");
         Warning("Cannot prevent core dumps!");
      }
   }
   SetMemoryLimit(h_parms->mem_limit);

   return state;
}

void print_help(FILE* out)
{
   fprintf(out, "\n\
E " VERSION " \"" E_NICKNAME "\"\n\
\n\
Usage: " NAME " [options] [files]\n\
\n\
Read a set of first-order clauses and formulae and try to refute it.\n\
\n");
   PrintOptions(stdout, opts, "Options:\n\n");
   fprintf(out, "\n\n" E_FOOTER);
}


/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/