#!/usr/bin/env python2.7
# encoding: utf-8

from feature_extractor import FeatureExtractor

import os
import sys
import re
import shutil

class SATFeatureExtractor(FeatureExtractor):
    def __init__(self, args):
        super(SATFeatureExtractor, self).__init__(args)

    def default_features(self):
        base_features = [
            'MpSAT-nvarsOrig',
            'MpSAT-nclausesOrig',
            'MpSAT-nvars',
            'MpSAT-nclauses',
            'MpSAT-reducedVars',
            'MpSAT-reducedClauses',
            'MpSAT-vars-clauses-ratio',
            'MpSAT-POSNEG-RATIO-CLAUSE-mean',
            'MpSAT-POSNEG-RATIO-CLAUSE-coeff-variation',
            'MpSAT-POSNEG-RATIO-CLAUSE-min',
            'MpSAT-POSNEG-RATIO-CLAUSE-max',
            'MpSAT-POSNEG-RATIO-CLAUSE-entropy',
            'MpSAT-VCG-CLAUSE-mean',
            'MpSAT-VCG-CLAUSE-coeff-variation',
            'MpSAT-VCG-CLAUSE-min',
            'MpSAT-VCG-CLAUSE-max',
            'MpSAT-VCG-CLAUSE-entropy',
            'MpSAT-UNARY',
            'MpSAT-BINARY+',
            'MpSAT-TRINARY+',
            'MpSAT-VCG-VAR-mean',
            'MpSAT-VCG-VAR-coeff-variation',
            'MpSAT-VCG-VAR-min',
            'MpSAT-VCG-VAR-max',
            'MpSAT-VCG-VAR-entropy',
            'MpSAT-POSNEG-RATIO-VAR-mean',
            'MpSAT-POSNEG-RATIO-VAR-stdev',
            'MpSAT-POSNEG-RATIO-VAR-min',
            'MpSAT-POSNEG-RATIO-VAR-max',
            'MpSAT-POSNEG-RATIO-VAR-entropy',
            'MpSAT-HORNY-VAR-mean',
            'MpSAT-HORNY-VAR-coeff-variation',
            'MpSAT-HORNY-VAR-min',
            'MpSAT-HORNY-VAR-max',
            'MpSAT-HORNY-VAR-entropy',
            'MpSAT-horn-clauses-fraction',
            'MpSAT-VG-mean',
            'MpSAT-VG-coeff-variation',
            'MpSAT-VG-min',
            'MpSAT-VG-max',
            'MpSAT-CG-mean',
            'MpSAT-CG-coeff-variation',
            'MpSAT-CG-min',
            'MpSAT-CG-max',
            'MpSAT-CG-entropy',
            'MpSAT-cluster-coeff-mean',
            'MpSAT-cluster-coeff-coeff-variation',
            'MpSAT-cluster-coeff-min',
            'MpSAT-cluster-coeff-max',
            'MpSAT-cluster-coeff-entropy',
            'MpSAT-DIAMETER-mean',
            'MpSAT-DIAMETER-coeff-variation',
            'MpSAT-DIAMETER-min',
            'MpSAT-DIAMETER-max',
            'MpSAT-DIAMETER-entropy',
            'MpSAT-cl-num-mean',
            'MpSAT-cl-num-coeff-variation',
            'MpSAT-cl-num-min',
            'MpSAT-cl-num-max',
            'MpSAT-cl-num-q90',
            'MpSAT-cl-num-q10',
            'MpSAT-cl-num-q75',
            'MpSAT-cl-num-q25',
            'MpSAT-cl-num-q50',
            'MpSAT-cl-size-mean',
            'MpSAT-cl-size-coeff-variation',
            'MpSAT-cl-size-min',
            'MpSAT-cl-size-max',
            'MpSAT-cl-size-q90',
            'MpSAT-cl-size-q10',
            'MpSAT-cl-size-q75',
            'MpSAT-cl-size-q25',
            'MpSAT-cl-size-q50',
            'MpSAT-SP-bias-mean',
            'MpSAT-SP-bias-coeff-variation',
            'MpSAT-SP-bias-min',
            'MpSAT-SP-bias-max',
            'MpSAT-SP-bias-q90',
            'MpSAT-SP-bias-q10',
            'MpSAT-SP-bias-q75',
            'MpSAT-SP-bias-q25',
            'MpSAT-SP-bias-q50',
            'MpSAT-SP-unconstraint-mean',
            'MpSAT-SP-unconstraint-coeff-variation',
            'MpSAT-SP-unconstraint-min',
            'MpSAT-SP-unconstraint-max',
            'MpSAT-SP-unconstraint-q90',
            'MpSAT-SP-unconstraint-q10',
            'MpSAT-SP-unconstraint-q75',
            'MpSAT-SP-unconstraint-q25',
            'MpSAT-SP-unconstraint-q50',
            'MpSAT-saps_BestSolution_Mean',
            'MpSAT-saps_BestSolution_CoeffVariance',
            'MpSAT-saps_FirstLocalMinStep_Mean',
            'MpSAT-saps_FirstLocalMinStep_CoeffVariance',
            'MpSAT-saps_FirstLocalMinStep_Median',
            'MpSAT-saps_FirstLocalMinStep_Q.10',
            'MpSAT-saps_FirstLocalMinStep_Q.90',
            'MpSAT-saps_BestAvgImprovement_Mean',
            'MpSAT-saps_BestAvgImprovement_CoeffVariance',
            'MpSAT-saps_FirstLocalMinRatio_Mean',
            'MpSAT-saps_FirstLocalMinRatio_CoeffVariance',
            'MpSAT-gsat_BestSolution_Mean',
            'MpSAT-gsat_BestSolution_CoeffVariance',
            'MpSAT-gsat_FirstLocalMinStep_Mean',
            'MpSAT-gsat_FirstLocalMinStep_CoeffVariance',
            'MpSAT-gsat_FirstLocalMinStep_Median',
            'MpSAT-gsat_FirstLocalMinStep_Q.10',
            'MpSAT-gsat_FirstLocalMinStep_Q.90',
            'MpSAT-gsat_BestAvgImprovement_Mean',
            'MpSAT-gsat_BestAvgImprovement_CoeffVariance',
            'MpSAT-gsat_FirstLocalMinRatio_Mean',
            'MpSAT-gsat_FirstLocalMinRatio_CoeffVariance',
            'MpSAT-lobjois-mean-depth-over-vars',
            'MpSAT-lobjois-log-num-nodes-over-vars',
            'meta-time-MpSAT-Basic-featuretime',
            'meta-time-MpSAT-CG-featuretime',
            'meta-time-MpSAT-DIAMETER-featuretime',
            'meta-time-MpSAT-KLB-featuretime',
            'meta-time-MpSAT-Pre-featuretime',
            'meta-time-MpSAT-cl-featuretime',
            'meta-time-MpSAT-lobjois-featuretime',
            'meta-time-MpSAT-ls-gsat-featuretime',
            'meta-time-MpSAT-ls-saps-featuretime',
            'meta-time-MpSAT-sp-featuretime',
        ]

        defaults = { key : self.sentinel_value for key in base_features }

        return defaults

    def extract(self, domain_path, instance_path):
        features = self.default_features()

        path_to_mp = "%s/sat/Mp" % (self.abs_script_directory)
        mp_command = [path_to_mp, "-F", "10", "-T", "10", "-O", "-b", "translatedInstance", domain_path, instance_path]

        try:
            output_directory = self.execute_command_with_runsolver(mp_command, None, None)

            cnf_file = "%s/translatedInstance.010.cnf" % (output_directory)
            if os.path.exists(cnf_file) and os.path.isfile(cnf_file):
                path_to_zilla_extractor = "%s/sat/bin/featuresSAT12" % (self.abs_script_directory)
                zilla_command = [path_to_zilla_extractor, "-base", "-sp", "-dia", "-cl", "-ls", "-lobjois", "translatedInstance.010.cnf", "MpSAT-features.csv"]

                self.execute_command_with_runsolver(zilla_command, output_directory, None)

                feature_file = "%s/MpSAT-features.csv" % output_directory
                if os.path.exists(feature_file) and os.path.isfile(feature_file):
                    with open(feature_file, 'r') as f:
                        line = f.readline().lstrip().rstrip()
                        feature_names = line.split(',')

                        line = f.readline().lstrip().rstrip()
                        feature_values = line.split(',')

                        sat_features = self.extract_sat_features(feature_names, feature_values)
                        features.update(sat_features)

        except Exception as e:
            print "Exception running the SAT translation: %s" % (str(e))
        finally:
            shutil.rmtree(output_directory)

        return features

    def extract_sat_features(self, names, values):
        sat_features = {}

        time_feature_indices = [6, 21, 42, 53, 59, 78, 97, 109, 121, 124]

        if len(names) == len(values):
            for index in range(len(names)):
                # remove the MpSAT- prefix
                name = names[index]
                value = values[index]

                if index in time_feature_indices:
                    sat_features["meta-time-MpSAT-%s" % name] = value
                else:
                    sat_features["MpSAT-%s" % name] = value

        return sat_features
