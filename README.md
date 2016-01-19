## planning-features

This project intends to be the most comprehensive and robust platform possible
for extracting scalar features from PDDL domains and problem instances for AI planning
problems.

We currently extract over 300 features from several broad categories, including
analysis of the PDDL and finite-domain \(FDR\) representations, FDR
causal graph and domain-transition graph structure, Boolean satisfiability problem representation,
and features obtained from short *probing* runs of several state-of-the-art planning algorithms.

Feature values can be output in CSV and/or JSON format, either to a file or to standard output.

For \(somewhat\) detailed installation instructions, see `INSTALLATION.md`

If you would like to contribute to the project, please have a look at `CONTRIBUTING.md`

This project is distributed under the Affero General Public License v3, for more information see `LICENSE-AGPL-v3.txt`.
Component projects and dependencies are included with permission of their authors, often with their own license terms.
Please inspect the appropriate subdirectories closely for details.

### Running the extractor

 * In order to extract features for a given PDDL domain and problem instance, simply execute the top-level extractor script
   with the domain and instance as arguments:

   `$ python <path to extractor>/planning-features/extract_planning_features.py --domain-file <path to domain> --instance-file <path to problem instance>`

 * This will extract all features and print the result to standard output in CSV format \(see below\)

### JSON output

 * Use the `--json-output-file` argument to pass a path where computed feature values should be stored in JSON format.
 * This file will be created anew rather than being appended to, and will currently **be overwritten** if it already exists.
 * The JSON format is:

    {
        "instance_features" : {
            'instance1 path' : {
                'feature1' : value1,
                'feature2' : value2,
                ...,
                'featureN' : valueN,
            },
            'instance2 path' : {
                'feature1' : value1,
                'feature2' : value2,
                ...,
                'featureN' : valueN,
            },
        }
    }

### CSV output

 * Use the `--csv-output-file` argument to pass a path where computed feature values should be stored in CSV format.
 * This file will be created anew rather than being appended to, and will currently **be overwritten** if it already exists.
 * There is a header printed \(unless `--no-csv-header` is used\), followed by one row per problem instance.
 * Column format is `problem instance,feature1,feature2,feature3,feature4,feature5,...,featureN`
 * Problem instance will be "-delimited, the remaining numeric columns have no delimiter

### Bulk extraction

 * If you want to extract features for more than one &lt;problem, domain&gt; pair at a time, you may replace the
   `--domain-file` and `--instance-file` arguments with a single `--bulk-extraction-file` argument with a file path containing
   the &lt;problem, domain&gt; pairs.
 * This file should be in CSV format, with the domain path in column 1 and problem instance in column 2.
 * A header row is assumed, and the paths in each column should be "-delimited

### Contributors

 * Chris Fawcett \(Project lead, extractor design and implementation\)
 * Mauro Vallati \(LPG preprocessing implementation\)
 * Frank Hutter
 * Joerg Hoffmann \(Torchlight extractor implementation\)
 * Kevin Leyton-Brown
 * Holger Hoos

### Papers

 * *Improved Features for Runtime Prediction of Domain-Independent Planners*  
   Chris Fawcett, Mauro Vallati, Frank Hutter, Joerg Hoffmann, Holger H. Hoos, Kevin Leyton-Brown  
   Proceedings of the 24th International Conference on Automated Planning and Scheduling \(ICAPS-14\), 2014.

### Third-party components

This project utilizes the work of several other groups, including:

 * [The Fast Downward planning system](http://www.fast-downward.org)
 * [The LPG planner](http://lpg.ing.unibs.it)
 * [Torchlight](https://fai.cs.uni-saarland.de/hoffmann/ff.html#torchlight)
 * [Runsolver](http://www.cril.univ-artois.fr/~roussel/runsolver)
 * [SATzilla](http://www.cs.ubc.ca/labs/beta/Projects/SATzilla/)
 * [Madagascar](http://users.ics.aalto.fi/rintanen/jussi/satplan.html)
