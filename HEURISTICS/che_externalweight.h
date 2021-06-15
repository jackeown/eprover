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

#ifndef CHE_ExternalWeightFun

#define CHE_ExternalWeightFun

#include <che_wfcb.h>

/*---------------------------------------------------------------------*/
/*                    Data type declarations                           */
/*---------------------------------------------------------------------*/



/*---------------------------------------------------------------------*/
/*                Exported Functions and Variables                     */
/*---------------------------------------------------------------------*/

WFCB_p ExternalWeightInit(ClausePrioFun prio_fun);

WFCB_p ExternalWeightParse(Scanner_p in, OCB_p ocb, ProofState_p state);

double ExternalWeightCompute(void* data, Clause_p clause);

void   ExternalWeightExit(void* data);


#endif

/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/





