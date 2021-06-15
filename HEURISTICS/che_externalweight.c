/*-----------------------------------------------------------------------

File  : che_externalweight.h

Author: John McKeown

Contents

  External Evaluation of a clause/

  Copyright 2021 by the author.
  This code is released under the GNU General Public Licence and
  the GNU Lesser General Public License.
  See the file COPYING in the main E directory for details..
  Run "eprover -h" for contact information.

-----------------------------------------------------------------------*/

#include "che_externalweight.h"



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
// Function: ExternalWeightInit()
//
//   Return an initialized WFCB for External evaluation.
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

WFCB_p ExternalWeightInit(ClausePrioFun prio_fun)
{
   double *data;

   data = SizeMalloc(sizeof(double));
   *data = 0.0;

   return WFCBAlloc(ExternalWeightCompute, prio_fun, ExternalWeightExit, data);
}


/*-----------------------------------------------------------------------
//
// Function: ExternalWeightParse()
//
//   Parse a ExternalWeight-declaration.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

WFCB_p ExternalWeightParse(Scanner_p in, OCB_p ocb, ProofState_p state)
{
   ClausePrioFun prio_fun;

   AcceptInpTok(in, OpenBracket);
   prio_fun = ParsePrioFun(in);
   AcceptInpTok(in, CloseBracket);

   return ExternalWeightInit(prio_fun);
}



/*-----------------------------------------------------------------------
//
// Function: ExternalWeightCompute()
//
//   Compute an evaluation for a clause.
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

double ExternalWeightCompute(void* data, Clause_p clause)
{
   double *local = data;

   *local = (*local)+1.0;
   return *local;
}


/*-----------------------------------------------------------------------
//
// Function: ExternalWeightExit()
//
//   Free the data entry in a External WFCB.
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

void ExternalWeightExit(void* data)
{
   SizeFree(data, sizeof(double));
}


/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/


