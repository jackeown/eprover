/*-----------------------------------------------------------------------

File  : pcl_steps.c

Author: Stephan Schulz

Contents

  Individual PCL steps and related stuff. 

  Copyright 1998, 1999 by the author.
  This code is released under the GNU General Public Licence.
  See the file COPYING in the main CLIB directory for details.
  Run "eprover -h" for contact information.

Changes

<1> Thu Mar 30 19:04:05 MET DST 2000
    New

-----------------------------------------------------------------------*/

#include "pcl_steps.h"


/*---------------------------------------------------------------------*/
/*                        Global Variables                             */
/*---------------------------------------------------------------------*/


/*---------------------------------------------------------------------*/
/*                      Forward Declarations                           */
/*---------------------------------------------------------------------*/


/*---------------------------------------------------------------------*/
/*                         Internal Functions                          */
/*---------------------------------------------------------------------*/



/*---------------------------------------------------------------------*/
/*                         Exported Functions                          */
/*---------------------------------------------------------------------*/


/*-----------------------------------------------------------------------
//
// Function: PCLStepFree()
//
//   Free a PCL step.
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

void PCLStepFree(PCLStep_p junk)
{
   assert(junk && junk->id && junk->clause && junk->just);

   PCLIdFree(junk->id);
   ClauseFree(junk->clause);
   PCLExprFree(junk->just);
   if(junk->extra)
   {
      FREE(junk->extra);
   }
   PCLStepCellFree(junk);
}


/*-----------------------------------------------------------------------
//
// Function: PCLStepParse()
//
//   Parse a PCL step.
//
// Global Variables: -
//
// Side Effects    : Input, memory operations
//
/----------------------------------------------------------------------*/

PCLStep_p PCLStepParse(Scanner_p in, TB_p bank)
{
   PCLStep_p handle = PCLStepCellAlloc();
   
   assert(in);
   assert(bank);
   
   handle->properties = PCLNoProp;
   PCLStepResetTreeData(handle, false);
   handle->id = PCLIdParse(in);
   AcceptInpTok(in, Colon);
   handle->clause = ClausePCLParse(in, bank);
   AcceptInpTok(in, Colon);
   handle->just = PCLFullExprParse(in);
   if(TestInpTok(in, Colon))
   {
      NextToken(in);
      CheckInpTok(in, Name|PosInt);
      handle->extra_string=TestInpTok(in,String)?true:false;
      handle->extra = DStrCopy(AktToken(in)->literal);
      NextToken(in);
   }    
   else
   {
      handle->extra = NULL;
   }
   ClauseDelProp(handle->clause, CPIsProofClause);
   return handle;
}


/*-----------------------------------------------------------------------
//
// Function: PCLStepPrintExtra()
//
//   Print a PCL step.
//
// Global Variables: -
//
// Side Effects    : Output
//
/----------------------------------------------------------------------*/

void PCLStepPrintExtra(FILE* out, PCLStep_p step, bool data)
{
   assert(step);

   PCLIdPrintFormatted(out, step->id, true);
   fputs(" : ", out);
   ClausePCLPrint(out, step->clause, true);
   fputs(" : ", out);
   PCLFullExprPrint(out, step->just);
   if(step->extra)
   {
      fputs(" : ", out);
      if(step->extra_string)
      {
	 fprintf(out, "\"%s\"", step->extra);
      }
      else
      {
	 fprintf(out, "%s", step->extra);
      }	 
   }
   if(data)
   {
      fprintf(out, " /* %#8X %6ld %6ld %3ld %3ld %3ld %3ld %4.3f */",
	      step->properties,
	      step->proof_dag_size,
	      step->proof_tree_size,
	      step->active_pm_refs,
	      step->other_generating_refs,
	      step->active_simpl_refs,
	      step->passive_simpl_refs,
	      step->lemma_quality);
   }
}


/*-----------------------------------------------------------------------
//
// Function: PCLStepIdCompare()
//
//   Compare two PCL steps by idents (forPTreeObj-Operations). 
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

int PCLStepIdCompare(PCLStep_p step1, PCLStep_p step2)
{
   return PCLIdCompare(step1->id, step2->id);
}


/*-----------------------------------------------------------------------
//
// Function: PCLStepResetTreeData()
//
//   Reset all counters and size data elements in the step to 0.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

void PCLStepResetTreeData(PCLStep_p step, bool just_weights)
{
   step->proof_dag_size        = PCLNoWeight;
   step->proof_tree_size       = PCLNoWeight;
   if(!just_weights)
   {
      step->active_pm_refs        = 0;
      step->other_generating_refs = 0;
      step->active_simpl_refs     = 0;  
      step->passive_simpl_refs    = 0;  
      step->lemma_quality         = 0.0;
      PCLStepDelProp(step,PCLIsLemma|PCLIsMarked);
   }
}


/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/


