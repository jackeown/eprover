/*-----------------------------------------------------------------------

File  : ekb_ginsert.c

Author: Stephan Schulz

Contents
 
  Generate new training examples from protocol and insert it into a
  knowledge base.

  Copyright 1998, 1999 by the author.
  This code is released under the GNU General Public Licence.
  See the file COPYING in the main CLIB directory for details.
  Run "eprover -h" for contact information.

Changes

<1> Wed Jul 28 16:21:33 MET DST 1999
    New

-----------------------------------------------------------------------*/

#include <cio_commandline.h>
#include <cio_fileops.h>
#include <cio_tempfile.h>
#include <cle_kbinsert.h>
#include <can_treeanalyze.h>
#include <cio_signals.h>

/*---------------------------------------------------------------------*/
/*                  Data types                                         */
/*---------------------------------------------------------------------*/

#define VERSION "0.1dev"

typedef enum
{
   OPT_NOOPT=0,
   OPT_HELP,
   OPT_VERSION,
   OPT_VERBOSE,
   OPT_KB,
   OPT_NAME
}OptionCodes;



/*---------------------------------------------------------------------*/
/*                        Global Variables                             */
/*---------------------------------------------------------------------*/

OptCell opts[] =
{
   {OPT_HELP, 
    'h', "help", 
    NoArg, NULL,
    "Print a short description of program usage and options."},

   {OPT_VERSION,
    '\0', "version",
    NoArg, NULL,
    "Print the version number of the program."},

   {OPT_VERBOSE, 
    'v', "verbose", 
    OptArg, "1",
    "Verbose comments on the progress of the program."},

   {OPT_NAME,
    'n', "name",
    ReqArg, NULL,
    "Give the name of the new problem. If not given, the program will "
    "take the name of the first input file, or, if <stdin> is read, a"
    " name of the form '__problem__i', where i is magically computed "
    " from the existing knowledge base."},

   {OPT_KB,
    'k',"knowledge-base",
    ReqArg, NULL,
    "Select the knowledge base. If not given, select E_KNOWLEDGE."},
    
   {OPT_NOOPT,
    '\0', NULL,
    NoArg, NULL,
    NULL}
};

char* ex_name = NULL;
char* kb_name = "E_KNOWLEDGE";

/*---------------------------------------------------------------------*/
/*                      Forward Declarations                           */
/*---------------------------------------------------------------------*/

CLState_p process_options(int argc, char* argv[]);
void print_help(FILE* out);

/*---------------------------------------------------------------------*/
/*                         Internal Functions                          */
/*---------------------------------------------------------------------*/


int main(int argc, char* argv[])
{
   CLState_p       state;
   DStr_p          name, store_file;
   FILE            *out;
   ExampleSet_p    proof_examples;
   AnnoSet_p       clause_examples;
   TB_p            annoterms;
   Sig_p           reserved_symbols;
   Scanner_p       in;
   KBDesc_p        kb_desc;
   char            defaultname[30];
   PStack_p        tmpfileinfo;
   /* int             i; */
   /* InfState_p      infstate1, infstate2;    */

   assert(argv[0]);

   InitOutput();
   InitError("ekb_ginsert");
   atexit(TempFileCleanup);
   ESignalSetup(SIGTERM);
   ESignalSetup(SIGINT);

   OutputLevel = 0;
   state = process_options(argc, argv);
   
   if(!ex_name && state->argv[0] && (strcmp(state->argv[0], "-")!= 0))
   {
      ex_name = state->argv[0];
   }   
   if(state->argc ==  0)
   {
      CLStateInsertArg(state, "-");
   }  
   
   name = DStrAlloc();
   
   /* Step 1: Read existing files: problems and kb_description to find
      out name ane parameters. */

   proof_examples = ExampleSetAlloc();
   in = CreateScanner(StreamTypeFile, 
		      KBFileName(name, kb_name, "problems"),
		      true, NULL);
   ExampleSetParse(in, proof_examples);
   DestroyScanner(in);
   
   in = CreateScanner(StreamTypeFile, 
		      KBFileName(name, kb_name, "description"),
		      true, NULL);
   kb_desc = KBDescParse(in);
   DestroyScanner(in);

   VERBOUT("Parameter files parsed successfully\n");
   
   /* Step 2: Finally determine name and check validity */
   
   if(!ex_name)
   {
      sprintf(defaultname, "__problem__%ld",
	      proof_examples->count+1);
      ex_name = defaultname;
   }
   if(ExampleSetFindName(proof_examples, ex_name))
   {
      DStr_p error = DStrAlloc();

      DStrAppendStr(error, "Example name '");
      DStrAppendStr(error, ex_name);
      DStrAppendStr(error, "' already in use");
      Error(DStrView(error), USAGE_ERROR);

      DStrFree(error);
   }

   VERBOUTARG("New example will use name ", ex_name);
   
   /* Step 3: Generate examples directly into example FILE (this part
      mostly taken from direct_examples)  */

   VERBOUT("Generating training examples\n");

   store_file = DStrAlloc();
   DStrAppendStr(store_file, KBFileName(name, kb_name, "FILES/"));
   DStrAppendStr(store_file, ex_name);
   
   out = OutOpen(DStrView(store_file));
   
   if(state->argc ==  0)
   {
      CLStateInsertArg(state, "-");
   }
   tmpfileinfo = CLStateCreateTempFiles(state);
   
   ClausesHaveLocalVariables = false; /* We need consistent
                                         name->variable mappings in
                                         this application! */
   /* infstate1 = InfStateAlloc();   
   infstate1->print_clause_evals = false;
   infstate1->print_clause_mods  = false;
   infstate1->print_clause_stats = false;
 
   infstate2 = InfStateAlloc();   
   infstate2->print_clause_evals = kb_desc->select_eval;
   infstate2->print_clause_mods  = !kb_desc->select_eval;
   infstate2->print_clause_stats = true;

   for(i=0; state->argv[i]; i++)
   {
      in = CreateScanner(StreamTypeFile, state->argv[i] , true, NULL);      
      InfStateInfListParse(in, out, infstate1);      
      DestroyScanner(in);
   }
   infstate2->created_count = infstate1->created_count;
   infstate2->processed_count = infstate1->processed_count; 
   infstate2->update_inf_inc = 0;
   
   ProofSetClauseStatistics(infstate1, 0, 0, 0, 0, PROOF_DIST_INFINITY);
   InfStateSelectExamples(infstate1, kb_desc->neg_proportion, 
			  kb_desc->fail_neg_examples);
   InfStateStoreClauseInfo(&(infstate2->watch_clauses), infstate1);
   
   fprintf(out, "# Axioms:\n");
   ClauseSetPrint(out, infstate1->axioms, true);
   fprintf(out, ".\n\n# Examples:\n");
   InfStateFree(infstate1);
     
   for(i=0; state->argv[i]; i++)
   {
      in = CreateScanner(StreamTypeFile, state->argv[i] , true, NULL);      
      InfStateInfListParse(in, out, infstate2);      
      DestroyScanner(in);
   }      
   InfStateFree(infstate2);
   CLStateDestroyTempFiles(state, tmpfileinfo);
   OutClose(out);
   */ 
   /* Step 4: Now read the remaining files (signature, clausepatterns)
    */

   VERBOUT("Parsing data files\n");

   reserved_symbols = SigAlloc();
   
   in = CreateScanner(StreamTypeFile, 
                      KBFileName(name, kb_name, "signature"),
                      true, NULL);
   SigParse(in, reserved_symbols, true);
   DestroyScanner(in);

   in = CreateScanner(StreamTypeFile, 
                      KBFileName(name, kb_name, "clausepatterns"),
                      true, NULL);

   annoterms = TBAlloc(TPIgnoreProps, reserved_symbols);
   clause_examples = AnnoSetParse(in, annoterms, KB_ANNOTATION_NO);
   DestroyScanner(in);


   /* Step 5: Integrate new examples into existing structures */
   
   VERBOUT("Integrating new examples\n");

   in = CreateScanner(StreamTypeFile, DStrView(store_file), true,
		      NULL);
   
   KBParseExampleFile(in, ex_name, proof_examples, clause_examples,
		      reserved_symbols);
   DestroyScanner(in);
   DStrFree(store_file);
      
   /* Step 6: Write everything back: problems, clausepatterns */

   VERBOUT("Writing example files\n");

   out = OutOpen(KBFileName(name, kb_name, "clausepatterns"));
   AnnoSetPrint(out, clause_examples);
   OutClose(out);
   
   out = OutOpen(KBFileName(name, kb_name, "problems"));
   ExampleSetPrint(out, proof_examples); 
   OutClose(out);

   /* Finally clean up */

   DStrFree(name);
   KBDescFree(kb_desc);
   AnnoSetFree(clause_examples);
   annoterms->sig = NULL;
   TBFree(annoterms);
   SigFree(reserved_symbols);
   ExampleSetFree(proof_examples);
   CLStateFree(state);
#ifdef CLB_MEMORY_DEBUG
   MemFlushFreeList();
   MemDebugPrintStats(stdout);
#endif
   
   return 0;
}


/*-----------------------------------------------------------------------
//
// Function: process_options()
//
//   Read and process the command line option, return (the pointer to)
//   a CLState object containing the remaining arguments.
//
// Global Variables: 
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
	    break;
      case OPT_VERSION:
	    printf("ekb_ginsert " VERSION "\n");
	    exit(NO_ERROR);
	    break;	    
      case OPT_KB:
	    kb_name = arg;
	    break;
      case OPT_NAME:
	    ex_name = arg;
	    break;	     
     default:
	 assert(false);
	 break;
      }
   }
   return state;
}

void print_help(FILE* out)
{
   fprintf(out, "\n\
\n\
make_kb " VERSION "\n\
\n\
Usage: THIS IS BROKEN AT THE MOMENT ekb_ginsert [options] [name]\n\
\n\
Generate a set of training examples from an E inference list and\n\
insert it into a knowledge base.\n\n"); 
   PrintOptions(stdout, opts);
   fprintf(out, "\n\
Copyright 1999 by Stephan Schulz, schulz@informatik.tu-muenchen.de\n\
\n\
This program is a part of the support structure for the E equational\n\
theorem prover. You can find the latest version of the E distribution\n\
as well as additional information at\n\
http://wwwjessen.informatik.tu-muenchen.de/~schulz/WORK/eprover.html.\n\
\n\
This program is free software; you can redistribute it and/or modify\n\
it under the terms of the GNU General Public License as published by\n\
the Free Software Foundation; either version 2 of the License, or\n\
(at your option) any later version.\n\
\n\
This program is distributed in the hope that it will be useful,\n\
but WITHOUT ANY WARRANTY; without even the implied warranty of\n\
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the\n\
GNU General Public License for more details.\n\
\n\
You should have received a copy of the GNU General Public License\n\
along with this program (it should be contained in the top level\n\
directory of the distribution in the file COPYING); if not, write to\n\
the Free Software Foundation, Inc., 59 Temple Place, Suite 330,\n\
Boston, MA  02111-1307 USA\n\
\n\
The original copyright holder can be contacted as\n\
\n\
Stephan Schulz\n\
Technische Universitaet Muenchen\n\
Fakultaet fuer Informatik\n\
Arcisstrasse 20\n\
D-80290 Muenchen\n\
Germany\n\
");

}


/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/


