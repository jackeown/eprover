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


typedef struct {
  int clausePipe;
  int scorePipe;
  long* nodeScratch;
  long* edgeIndexScratch;
  long* edgeAttrScratch;
  double* scoreScratch;
  Sig_p signature;
  StrTree_p symbolMap;
} ExternalWeightState_cell, *ExternalWeightState_p;


typedef struct {
  int shape[2];
  long* data;
} Matrix;

typedef struct {
  Matrix node_symbols;
  Matrix edge_index;
  Matrix edge_attr;
} PyG;


/*---------------------------------------------------------------------*/
/*                Exported Functions and Variables                     */
/*---------------------------------------------------------------------*/

WFCB_p ExternalWeightInit(ClausePrioFun prio_fun, ProofState_p state, char* clausePipePath, char* scorePipePath, char* symbolMapPath);

WFCB_p ExternalWeightParse(Scanner_p in, OCB_p ocb, ProofState_p state);

double ExternalWeightCompute(void* data, Clause_p clause);

void   ExternalWeightExit(void* data);


#endif

/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/




