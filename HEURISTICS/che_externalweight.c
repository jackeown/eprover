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
int nodeScratchSize = 1000;
int edgeIndexScratchSize = 10000;
int edgeAttrScratchSize = 5000;
int scoreScratchSize = 1000;


/*---------------------------------------------------------------------*/
/*                      Forward Declarations                           */
/*---------------------------------------------------------------------*/


/*---------------------------------------------------------------------*/
/*                         Internal Functions                          */
/*---------------------------------------------------------------------*/
PyG clauseToPyG_dumb(Clause_p clause, ExternalWeightState_p state){
   PyG dag;
   dag.node_symbols.shape[0] = 1;
   dag.node_symbols.shape[1] = 6;
   dag.node_symbols.data = SizeMalloc(6 * sizeof(long));
   for(int i=0; i<6; i++)
      dag.node_symbols.data[i] = i;
   dag.edge_index.shape[0] = 2;
   dag.edge_index.shape[1] = 20;
   dag.edge_index.data = SizeMalloc(40 * sizeof(long));
   for(int i=0; i<40; i++)
      dag.edge_index.data[i] = rand() % 6;
   dag.edge_attr.shape[0] = 20;
   dag.edge_attr.shape[1] = 1;
   dag.edge_attr.data = SizeMalloc(20 * sizeof(long));
   for(int i=0; i<20; i++)
      dag.edge_attr.data[i] = rand() % 20;
   return dag;
}


long translateFunCode(FunCode f, ExternalWeightState_p state){
   // printf("Translating FunCode...%ld\n", f);
   StrTree_p node;
   if(f < 0){
      char name[100];
      sprintf(name, "X%ld", -f);
      node = StrTreeFind(&(state->symbolMap), name);
   }
   else{
      char* name = state->signature->f_info[f].name;
      node = StrTreeFind(&(state->symbolMap), name);
   }

   if(node == NULL){
      printf("StrTreeFind Lookup failed for %ld (%s)\n", f, state->signature->f_info[f].name);
   }
   return node->val1.i_val;
}

long translateSymbolName(char* symbolName, ExternalWeightState_p state){
   return StrTreeFind(&(state->symbolMap), symbolName)->val1.i_val;
}




// TODO: Implement this.
PyG treeToDag(PyG tree){
   return tree;
}

long addNode(PyG* tree, long symbol){
   int index = tree->node_symbols.shape[0];

   tree->node_symbols.data[index] = symbol;
   tree->node_symbols.shape[0]++;

   return index;
}

void addEdge(PyG* tree, long type, long source, long dest){
   int num_edges = tree->edge_attr.shape[0];

   // add edge connection info
   tree->edge_index.data[(2 * num_edges)] = source;
   tree->edge_index.data[(2 * num_edges) + 1] = dest;
   tree->edge_index.shape[0]++;

   // add edge type info
   tree->edge_attr.data[num_edges] = type;
   tree->edge_attr.shape[0]++;
}

void includeTerm(Term_p term, PyG* tree, long parent, long childIdx, ExternalWeightState_p state){
   long child = addNode(tree, translateFunCode(term->f_code, state));
   addEdge(tree, childIdx, parent, child);

   for(int i=0; i<term->arity; i++){
      includeTerm(term->args[i], tree, child, i, state);
   }
}

void includePositiveLiteral(Eqn_p lit, PyG* tree, long parent, long childIdx, ExternalWeightState_p state){
   if(EqnIsEquLit(lit)){ // s = t and not s = $true
      long newNode = addNode(tree, translateSymbolName("=", state));
      addEdge(tree, childIdx, parent, newNode);
      includeTerm(lit->lterm, tree, newNode, 0, state);
      includeTerm(lit->rterm, tree, newNode, 1, state);
   }
   else{
      lit = EqnCanonize(lit);
      includeTerm(lit->lterm, tree, parent, 0, state);
   }
}

void includeLiteral(Eqn_p lit, PyG* tree, long parent, long childIdx, ExternalWeightState_p state){
   if(EqnIsPositive(lit)){
      long newNode = addNode(tree, translateSymbolName("~~", state));
      addEdge(tree, childIdx, parent, newNode);
      includePositiveLiteral(lit, tree, newNode, 0, state);
   }
   else{
      long newNode = addNode(tree, translateSymbolName("~", state));
      addEdge(tree, childIdx, parent, newNode);
      includePositiveLiteral(lit, tree, newNode, 0, state);
   }  
}




PyG clauseToPyG(Clause_p clause, ExternalWeightState_p state){
   // printf("clause to pyg starting...\n");
   // ClausePrint(stdout, clause, true);
   // printf("\n");
   return clauseToPyG_dumb(clause, state);

   // PyG tree;

   // tree.node_symbols.shape[0] = 0;
   // tree.node_symbols.shape[1] = 1;
   // tree.node_symbols.data = state->nodeScratch;

   // tree.edge_index.shape[0] = 0;
   // tree.edge_index.shape[1] = 2;
   // tree.edge_index.data = state->edgeIndexScratch;

   // tree.edge_attr.shape[0] = 0;
   // tree.edge_attr.shape[1] = 1;
   // tree.edge_attr.data = state->edgeAttrScratch;

   // long OR = addNode(&tree, translateSymbolName("|"));

   // long i=0;
   // for(Eqn_p lit = clause->literals; lit != NULL; lit=lit->next){
   //    includeLiteral(lit, &tree, OR, i++);
   // }

   // return tree;
}


void sendIntToPipe(int x, int pipe){
   write(pipe, &x, sizeof(x));
}

void sendBoolToPipe(bool b, int pipe){
   char c = b;
   write(pipe, &c, 1);
}

void sendMatrixToPipe(Matrix M, int pipe){
   write(pipe, M.shape, 2 * sizeof(int));
   write(pipe, M.data, M.shape[0] * M.shape[1] * sizeof(long));
}


int countClauses(Clause_p clauses){
   int n = 0;
   for(Clause_p c=clauses->succ; c != clauses; c=c->succ){
      n++;
   }
   return n;
}


void sendClauses(Clause_p clauses, ExternalWeightState_p state, bool context){

   sendBoolToPipe(context, state->clausePipe);
   sendIntToPipe(countClauses(clauses), state->clausePipe);

   // This for loop assumes that clauses is an "anchor" 
   // as shown in "eval_clause_set" in"cco_proofproc.c"
   for(Clause_p c=clauses->succ; c != clauses; c=c->succ){
      PyG tree = clauseToPyG(c, state);
      PyG dag = treeToDag(tree);

      sendMatrixToPipe(dag.node_symbols, state->clausePipe);
      sendMatrixToPipe(dag.edge_index, state->clausePipe);
      sendMatrixToPipe(dag.edge_attr, state->clausePipe);

      // TODO: Is this necessary?
      // free(dag.node_symbols.data);
      // free(dag.edge_index.data);
      // free(dag.edge_attr.data);
   }
}

void receiveScores(ExternalWeightState_p state){
   // printf("Receiving scores...\n");

   int numScores;
   read(state->scorePipe, &numScores, sizeof(int));

   for(int i=0; i<numScores; i++){
      read(state->scorePipe, state->scoreScratch + i, sizeof(double));
   }
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

WFCB_p ExternalWeightInit(ClausePrioFun prio_fun, ProofState_p state, char* clausePipePath, char* scorePipePath, char* symbolMapPath)
{
   printf("ExternalWeightInit...\n");

   // Set Up Named Pipes...
   ExternalWeightState_p data = SizeMalloc(sizeof(ExternalWeightState_cell));
   data->clausePipe = open(clausePipePath, O_WRONLY);
   data->scorePipe = open(scorePipePath, O_RDONLY);

   // Allocate buffers that the pipes will interact with...
   data->nodeScratch = SizeMalloc(nodeScratchSize * sizeof(long));
   data->edgeIndexScratch = SizeMalloc(edgeIndexScratchSize * sizeof(long));
   data->edgeAttrScratch = SizeMalloc(edgeAttrScratchSize * sizeof(long));
   data->scoreScratch = SizeMalloc(scoreScratchSize * sizeof(double));

   // Add signature to ExternalWeightState...
   data->signature = state->signature;

   // Read in symbolMap and identify symbol ints with f_codes in signature...
   data->symbolMap = StrTreeCellAllocEmpty();
   Scanner_p in = CreateScanner(StreamTypeFile, symbolMapPath, true, NULL, true);

   IntOrP dummy, n;
   dummy.i_val = 0;
   while(!TestInpTok(in, NoToken)){
      n.i_val = ParseInt(in);
      char* symbol = ParseContinous(in);
      ParseInt(in); // Throw away type (we don't use it here for now)

      StrTreeStore(&(data->symbolMap), symbol, n, dummy);
      // printf("Parsed symbol '%s' = %d\n", symbol, n.i_val);
   }

   //////////////////////// BEGIN SENDING CONTEXT CLAUSES ///////////////////////////////
   Clause_p negConjContextClausesAnchor = ClauseCellAlloc();
	Clause_p negHandle = negConjContextClausesAnchor;

	int numNegConjClauses = 0;
	Clause_p allHandle = state->axioms->anchor;
	for(int i=0; i < state->axioms->members; i++){
		allHandle = allHandle->succ;

		if(ClauseIsConjecture(allHandle)){
			numNegConjClauses++;
			negHandle->succ = ClauseFlatCopy(allHandle);
			negHandle = negHandle->succ;
         negHandle->succ = negConjContextClausesAnchor;
		}
	}

   sendClauses(negConjContextClausesAnchor, data, true);
   ////////////////////// FINISHED SENDING CONTEXT CLAUSES ///////////////////////////////
   
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
   AcceptInpTok(in, Comma);
   char* symbolMapPath = ParseFilename(in);

   AcceptInpTok(in, CloseBracket);

   return ExternalWeightInit(prio_fun, state, clausePipePath, scorePipePath, symbolMapPath);
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

double ExternalWeightCompute(void* data, Clause_p clauses)
{
   // printf("Sending clause for evaluation...\n");
   // ClausePrint(stdout, clauses, true); // for loop needed to see all of course
   // printf("\n");

   // Temporary hack for testing... //////
   Clause_p anchor = EmptyClauseAlloc();
   anchor->succ = clauses;
   Clause_p succ = clauses->succ;
   clauses->succ = anchor;
   ///////////////////////////////////////

   ExternalWeightState_p state = data;
   sendClauses(clauses, state, false);
   receiveScores(state);
   
   clauses->succ = succ;
   return state->scoreScratch[0]; // dummy return to keep this function having a double return type
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
   ExternalWeightState_p state = data;
   free(state->nodeScratch);
   free(state->edgeIndexScratch);
   free(state->edgeAttrScratch);
   free(state->scoreScratch);
   SizeFree(data, sizeof(ExternalWeightState_cell));
}


/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/


