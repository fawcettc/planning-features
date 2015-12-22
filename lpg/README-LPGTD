***************************************************************************
                       
                       User Instructions for LPG-td 

            Alfonso Gerevini, Alessandro Saetti and Ivan Serina              
               Dipartimento di Elettronica per l'Automazione	         
                          Universita' di Brescia           
                  Via Branze 38, I-25123, Brescia, Italy
                   {gerevini,saetti,serina}@ing.unibs.it 
                         http://lpg.ing.unibs.it/
         
                               August 2004                 

     The code of LPG-td is provided for research purposes only, in the 
     hope that it will be useful, but WITHOUT ANY WARRANTY. Commercial 
     users must contact the authors for licensing arrangement.

****************************************************************************
                                                          

LPG is a fully automated system for solving planning problems specified
using version 2.2 (2004) of the standard planning language PDDL. LPG-td 
is a new version of LPG including several extensions and improvements. 
LPG-td supports Timed Initial Literals and Derived Predicates, the two 
main new features of PDDL2.2.

"lpgtd-linux.tar.gz" is a complied version for Linux (Debian 3.0)
"lpgtd-win.tar.gz" is a compiled version for Windows (Windows 2000)


1. Installing the Compiled Code
-------------------------------

For Linux users:

- Copy lpgtd-linux.tar.gz into the directory where you want to have the 
  planner.

- From this directory run

      gunzip lpgtd-linux.tar.gz 
      tar xvf lpgtd-linux.tar 

For Windows users:

- Copy lpgtd-win.tar.gz into the directory where you want to have the
  planner.

- Use Winzip to unzip the files in this directory.

For both Linux and Windows users:

A directory called LPG-td will be generated including these files and 
subdirectories:

  README-LPGTD  -- this file 
  lpg-td        -- the executable code of the planner
  PSR           -- a directory containing two versions of the domain 
                   "PSR" and some test problems, which were used in the
                   4th International Planning Competition (IPC) 2004. 
  UMTS          -- a directory containing four versions of the domain
                   "UMTS" and some test problems, which were used in 
                   the 4th IPC.
                    
  PSR and UMTS are examples of recent standard planning domains/problems 
  that can be handled by our planner. Their description can be found in 
  the web page of the 4th IPC.
  Note that there are 2 different versions of PSR: "small" (the strips 
  version), and "middle" (the version with derived predicates).
  The UMTS domain has four versions: "temporal" (the temporal version), 
  "temporal-timewindows" (the version with timed initial literals),
  "flaw-temporal" (the temporal version containing an additional flaw 
  action), and "flaw-temporal-timewindows" (the version with timed 
  initial literals and the additional flaw action).


2. Running LPG-td
-----------------

2.1 Necessary Settings

In order to run the program (lpg-td) it is necessary to specify the value
of three parameters indicating: (a) a file containing a set of PDDL2.2
operators; (b) a file containing a planning problem (initial state and
goals of the problem) formalized in PDDL2.2; and (c) a running mode, 
which is either "speed", "quality" or "incremental quality" (also called
"bestquality"). 
(a) and (b) must be specified using

  -o <operator file name> 
  -f <problem file name>

(c) must be specified using one of the following three options

  -speed 
  -quality
  -n <max number of desired solutions>

  In speed mode, LPG-td finds a solution (of any quality) as quickly as
  possible.

  In quality mode, LPG-td is slower than in speed mode, but the planner 
  finds a solution with better quality. After having found a first solution,
  LPG-td automatically decides how much CPU-time is spent for improving it.
  
  In the incremental mode, LPG-td finds a sequence of solutions, each of
  which is written in a file with the standard name

     plan_<problem file name>_<solution number>.SOL

  When the number "x" of solutions specified for the incremental mode is 
  greater than 1, each solution computed is an improvement with respect to 
  the previous one (in terms of the plan metric indicated in the problem 
  file).  When x = 1, LPG-td works in speed mode.
  Note that only the last solution that is computed is shown on the screen 
  (while each solution is written in a different file).
  Moreover, x is an upper bound: it can happen that the system never finds 
  x solutions -- for example, because the i-th solution found (i < x) is 
  the best solution of the planning problem under consideration). 
  If LPG-td cannot find x solutions, it stops when it reaches the CPU-time 
  upper bound.   

  For example, "lpg-td -o op-file-name -f p-file-name -n 3" runs LPG-td
  using the operators specified in operator-file to produce (at most) 
  three plans solving the problem specified in problem-file.

===========================================================================


2.2 Optional Settings

LPG-td supports several additional settings, each of which has its own
default value.

  -p <string>

This option can be used to specify the path name of the directory containing 
the file of the operators and the file of the problem definition.  
Example: lpg-td -p /home/LPG/domains/ -o op-file-name -f p-file-name -speed

  -out <string> 

This option can be used to change the default name of the files containing 
the plans computed by LPG-td. 
For example, "lpg -o op-file-name -f p-file-name -n 2 -out myplan" produces 
two files (assuming that the planner finds two solutions) named 
"myplan_1.SOL" and "myplan_2.SOL".

  -noout

With this option no output file is produced.

  -v off

This option switches off the verbose output of LPG (the planner provides
only essential information).

  -search_steps <integer> 

Specifies the initial number of search steps after which the search is
restarted. After each search restart, this number is automatically 
incremented by a factor of 1.1. The default initial value for -search_steps 
is 500.  Note that for simple problems this value could be significantly 
reduced, obtaining better performance.

  -restarts <integer>

Specifies the maximum number of search restarts after which the search 
is repeated for a certain number of times (see the "-repeat" parameter).
After each restart, the value of some dynamic parameters (e.g., number 
of search step) is automatically changed. The default value of -restarts 
is 9.

  -repeats <integer>

Specifies the maximum number of times (repeats) the local search is
repeated to find the first solution. If no solution has been found within
the specified number of repeats (and the CPU-time limit for the local
search has not been exceeded), the best-first search is activated.
Each time the local search is repeated, the dynamic settings of the
planner (e.g., the number of search steps) are set to their initial value.
When LPG-td is run in quality mode or incremental mode ("-n x", x > 1), 
if a solution is found by the local search (under the specified CPU-time
limit and number of repeats), the local search is repeated until the
CPU-time limit of the local search is reached, or the number of solutions
specified by the "-n" parameter have been found. 
The default value of -repeats is 5.

  -noise <number between 0 and 1>

Specifies the initial noise value for Walkplan. Such value is dynamically
modified during each restart using a technique described in in Gerevini,
Saetti, Serina "An Empirical Analysis of Some Heuristic Features for Local 
Search in LPG", ICAPS'04. The default value of -noise is 0.1.

  -maxnoise

Specifies the maximum noise value that can (automatically) be reached by
the dynamic noise. 

  -static_noise

Switches off the dynamic noise during each restart. The value of the 
noise is fixed. The default value is 0.1, and it can be changed by using
the "-noise" parameter.

  -seed <integer>

Specifies the seed for the random number generator used by Walkplan 
(a stochastic local search procedure). By using the same seed number, 
it is possible to repeat identical runs. The output files containing the
solutions produced by LPG include the seed number used by the planner to
generate them. In the 4th IPC, we used "-seed 2004".

  -lowmemory              

With this option, the mutex relations between actions are computed at 
runtime (instead of being computed before searching). We recommend the 
use of this option only for very large problems.

  -cputime <number>       

Specifies the maximum CPU-time (in seconds) after which termination of 
the planning process is forced. The default value is 1800 (30 minutes).

  -cputime_localsearch <number>    

When all restarts of the local search have been performed without finding
a solution, LPG runs in a best-first search based on Joerg Hoffman's
implementation (FF package v2.3). This option specifies the maximum
CPU-time (in seconds) after which the best-first search starts. 
The default value is 1200 (20 minutes).

  -nobestfirst

With this option, LPG-td does not run best-first search.

  -onlybestfirst     

Forces the immediate run of the best-first search (no local search is 
performed). 

  -timesteps

This option can be used in STRIPS domains to define the plan quality 
metric as number of (Graphplan) time steps.