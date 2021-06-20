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

#include <fcntl.h>
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


PyG treeToDag(PyG tree){

}



PyG clauseToPyG(Clause_p clause){
   PyG dag;

   // Eqn_p lits = clause->literals;
   // Term_p lterm = lits->lterm;
   // Term_p rterm = lits->rterm;

   // FunCode f = lterm->f_code;
   // int arity = lterm->arity;
   // Term_p subterms = lterm->args;














   // dag.nodeVecs.shape[0] = 1;
   // dag.nodeVecs.shape[1] = 6;
   // dag.nodeVecs.data = SizeMalloc(6 * sizeof(long));
   // for(int i=0; i<6; i++)
   //    dag.nodeVecs.data[i] = i;


   // dag.edge_index.shape[0] = 2;
   // dag.edge_index.shape[1] = 20;
   // dag.edge_index.data = SizeMalloc(40 * sizeof(long));
   // for(int i=0; i<40; i++)
   //    dag.edge_index.data[i] = rand() % 6;
   

   // dag.edge_attr.shape[0] = 20;
   // dag.edge_attr.shape[1] = 1;
   // dag.edge_attr.data = SizeMalloc(20 * sizeof(long));
   // for(int i=0; i<20; i++)
   //    dag.edge_attr.data[i] = rand() % 20;

   return dag;
}

void sendContextToPipe(bool context, int pipe){
   char c = context;
   write(pipe, &c, 1);
}

void sendMatrixToPipe(Matrix M, int pipe){
   write(pipe, M.shape, 2 * sizeof(int));
   write(pipe, M.data, M.shape[0] * M.shape[1] * sizeof(long));
}

void sendClauseToPipe(Clause_p clause, int pipe, bool context){
   PyG dag = clauseToPyG(clause);

   sendContextToPipe(context, pipe);
   sendMatrixToPipe(dag.nodeVecs, pipe);
   sendMatrixToPipe(dag.edge_index, pipe);
   sendMatrixToPipe(dag.edge_attr, pipe);

   free(dag.nodeVecs.data);
   free(dag.edge_index.data);
   free(dag.edge_attr.data);
}

double receiveScoreFromPipe(int pipe){
   double buff;
   read(pipe, &buff, sizeof(double));
   return buff;
}


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

WFCB_p ExternalWeightInit(ClausePrioFun prio_fun, char* clausePipePath, char* scorePipePath)
{
   printf("ExternalWeightInit...\n");
   ExternalWeightState_p data = SizeMalloc(sizeof(ExternalWeightState_cell));

   data->clausePipePath = clausePipePath;
   data->clausePipe = open(clausePipePath, O_WRONLY);

   data->scorePipePath = scorePipePath;
   data->scorePipe = open(scorePipePath, O_RDONLY);

   printf("ExternalWeightInit WFCBAlloc starting...\n");
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
   printf("ExternalWeightParse...\n");

   ClausePrioFun prio_fun;

   AcceptInpTok(in, OpenBracket);

   prio_fun = ParsePrioFun(in);
   AcceptInpTok(in, Comma);
   char* clausePipePath = ParseFilename(in);
   AcceptInpTok(in, Comma);
   char* scorePipePath = ParseFilename(in);

   AcceptInpTok(in, CloseBracket);

   return ExternalWeightInit(prio_fun, clausePipePath, scorePipePath);
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
   printf("Sending clause for evaluation...");
   ExternalWeightState_p state = data;
   sendClauseToPipe(clause, state->clausePipe, false);

   double score = receiveScoreFromPipe(state->scorePipe);
   // double score = 3.0;
   printf("score = %lf\n", score);
   return score;
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
   SizeFree(data, sizeof(ExternalWeightState_cell));
}


/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/


