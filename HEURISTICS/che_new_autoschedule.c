/*-----------------------------------------------------------------------

File  : che_new_autoschedule.c

Author: Stephan Schulz

Contents

  Code that is automatically generated by 

Changes

<1> Tue May  2 22:07:17 GMT 2000
    Extracted from che_heuristics.c

-----------------------------------------------------------------------*/

#include "che_new_autoschedule.h"

#include "autoschedule_gen.vars"
#include "autoschedule_gen_multi.vars"

ScheduleCell* new_schedule = NEW_HO_SCHEDULE;

void print_config_name(FILE* out, const char* prefix, const char* config, int idx)
{
  DStr_p str = DStrAlloc();
  assert(strchr(config, '\n'));
  DStrAppendBuffer(str, (char*)config, strchr(config, '\n') - config);
  locked_fprintf(out, "# %s config(%d): %s\n", prefix, idx, DStrView(str));
  DStrFree(str);
}

int str_distance(const char* a, const char* b)
{
  int dist = 0;
  while(*a && *b)
  {
    dist += *a == *b ? 0 : 1;
    a++;
    b++;
  }
  dist += strlen(a);
  dist += strlen(b);
  return dist;
}

const char* class_to_heuristic(const char* problem_category, const char** categories,
                        const char** configurations, int num_categories, 
                        HeuristicParms_p params)
{
  int min_idx = -1;
  int min_dist = INT_MAX;
  for(int i=0; i<num_categories; i++)
  {
    for(int i=0; min_dist && i<num_categories; i++)
    {
      int dist = str_distance(categories[i], problem_category);
      if(dist == 0)
      {
        min_idx = i;
        min_dist = 0;
      }
      if (dist < min_dist)
      {
        min_dist = dist;  
        min_idx = i;
      }
    }
  }
  assert(min_idx >= 0);
  const char* configuration =  configurations[min_idx];
  Scanner_p in = CreateScanner(StreamTypeInternalString, (char*)configuration, true, NULL, true);
  HeuristicParmsParseInto(in, params, false); 
  DestroyScanner(in);
  return configuration;
}

const char* class_to_schedule(const char* problem_category, const char** categories,
                        const char* configurations[][SCHEDULE_SIZE], int num_categories, 
                        int attempt_idx, HeuristicParms_p params)
{
  int min_idx = -1;
  int min_dist = INT_MAX;
  for(int i=0; min_dist && i<num_categories; i++)
  {
    int dist = str_distance(categories[i], problem_category);
    if(dist == 0)
    {
      min_idx = i;
      min_dist = 0;
    }
    if (dist < min_dist)
    {
      min_dist = dist;  
      min_idx = i;
    }
  }
  assert(min_idx >= 0);
  const char* conf =  configurations[min_idx][attempt_idx];
  assert(attempt_idx < SCHEDULE_SIZE);
  Scanner_p in = CreateScanner(StreamTypeInternalString, (char*)conf, true, NULL, true);
  HeuristicParmsParseInto(in, params, false); 
  DestroyScanner(in);
  return conf;
}

void AutoHeuristicForRawCategory(const char* raw_category, HeuristicParms_p parms)
{
  const char* config = class_to_heuristic(raw_category, raw_categories, raw_confs, num_raw_categories, parms);
  locked_fprintf(stderr, "# raw_category: %s\n", raw_category);
  print_config_name(stderr, "raw", config, 0);
}

void ScheduleForRawCategory(const char* raw_category, int attempt_idx, HeuristicParms_p parms)
{
  const char* config = class_to_schedule(raw_category, multischedule_raw_categories, multischedule_raw_confs, 
                                         multischedule_raw_categories_len, attempt_idx, parms);
  locked_fprintf(stderr, "# raw_category(%d): %s\n", attempt_idx, raw_category);
  print_config_name(stderr, "raw", config, attempt_idx);
}

void AutoHeuristicForCategory(const char* category, HeuristicParms_p parms)
{
  const char* config = class_to_heuristic(category, categories, confs, num_categories, parms);
  locked_fprintf(stderr, "# category: %s\n", category);
  print_config_name(stderr, "after cnf", config, 0);
}

void ScheduleForCategory(const char* category, int attempt_idx, HeuristicParms_p parms)
{
  const char* config = class_to_schedule(category, multischedule_categories, multischedule_confs, 
                                         multischedule_categories_len, attempt_idx, parms);
  locked_fprintf(stderr, "# category(%d): %s\n", attempt_idx, category);
  // DBG_PRINT(stderr, "config: ", HeuristicParmsPrint(stderr, parms), ".\n");
  print_config_name(stderr, "after cnf", config, attempt_idx);
}

int GetAttemptIdx(const char* strategy_name)
{
  char* pref = "AutoNewSched_";
  return strstr(strategy_name, pref) ? atoi(strategy_name + strlen(pref)) : -1;
}

