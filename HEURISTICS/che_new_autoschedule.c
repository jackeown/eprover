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


typedef struct 
{
  char* key;
  char* value;
} StrStrPair;

typedef struct 
{
  char* key;
  ScheduleCell* value;
  int class_size; // how many problems were originally in the class used for scheduling
                  // (will be used for tie-breaking when choosing the class) 
} StrSchedPair;

#include "schedule.vars"

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

ScheduleCell* class_to_schedule(const char* problem_category, StrSchedPair* schedules)
{
  int min_idx = -1;
  int min_dist = INT_MAX;
  int max_class_size = INT_MIN;
  for(int i=0; min_dist && schedules[i].key; i++)
  {
    int dist = str_distance(schedules[i].key, problem_category);
    if(dist == 0)
    {
      min_idx = i;
      min_dist = 0;
    }
    else if (dist < min_dist)
    {
      min_dist = dist;  
      min_idx = i;
      max_class_size = schedules[i].class_size;
    }
    else if (dist == min_dist && schedules[i].class_size > max_class_size)
    {
      min_idx = i;
      max_class_size = schedules[i].class_size;
    }
  }
  assert(min_idx >= 0);
  if(min_dist)
  {
    fprintf(GlobalOut, "# partial match(%d): %s\n", min_dist, schedules[min_idx].key);
  }
  return schedules[min_idx].value;
}

ScheduleCell* GetPreprocessingSchedule(const char* problem_category)
{
  return class_to_schedule(problem_category, preproc_sched_map);
}

ScheduleCell* GetSearchSchedule(const char* problem_category)
{
  return class_to_schedule(problem_category, search_sched_map);
}

void GetHeuristicWithName(const char* name, HeuristicParms_p target)
{
  for(int i=0; conf_map[i].key; i++)
  {
    if(!strcmp(name, conf_map[i].key))
    {
      Scanner_p in = CreateScanner(StreamTypeInternalString, (char*)conf_map[i].value, 
                                   true, NULL, true);
      target->heuristic_def = NULL; // because the code below tries to free it,
                                    // even when it should not be freed.
      HeuristicParmsParseInto(in, target, false);
      DestroyScanner(in);
      return;
    }
  }
  fprintf(stderr, "Internal error -- configuration name %s not found.\n", name);
  SysError("exiting", -1);
}

ScheduleCell* GetDefaultSchedule()
{
  return _DEFAULT_SCHEDULE;
}