#!/usr/bin/env python2.7
# encoding: utf-8
'''
    Copyright (C) 2013-2016 Chris Fawcett (fawcettc@cs.ubc.ca)

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU Affero General Public License as
    published by the Free Software Foundation, either version 3 of the
    License, or (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Affero General Public License for more details.

    You should have received a copy of the GNU Affero General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
'''

from feature_extractor import FeatureExtractor

import os
import sys
import re
import shutil

class FDProbingFeatureExtractor(FeatureExtractor):
    def __init__(self, args):
        super(FDProbingFeatureExtractor, self).__init__(args)

        self.extractor_name = "fd-probing"

        self.requires_sas_representation = True

    def default_features(self):
        base_features = [
            'fdProbingReasonableOrdersRemoved',
            'fdProbingLandmarksDiscovered',
            'fdProbingLandmarksPercentageDisjunctive',
            'fdProbingLandmarksPercentageConjunctive',
            'fdProbingNumEdges',
            'fdProbingInitialLandmarks',
            'fdProbingGoalLandmarks',
            'fdProbingRatioGoalLandmarksOverInitialLandmarks',
            'fdProbingInitialHeuristicNum',
            'fdProbingInitialHeuristicDen',
            'fdProbingInitialGValue',
            'fdProbingFinalHeuristicNum',
            'fdProbingFinalHeuristicDen',
            'fdProbingFinalHeuristicGValue',
            'fdProbingPercentageImprovementNum',
            'fdProbingFinalStatesEvaluated',
        ]

        defaults = { key : self.sentinel_value for key in base_features }

        return defaults

    def extract(self, domain_path, instance_path):
        features = self.default_features()

        path_to_fd = "%s/fast-downward/search/downward" % (self.abs_script_directory)
        fd_command = [path_to_fd, "ipc", "seq-sat-lama-2011"]

        successful = False
        try:
            sas_path = "%s/output" % self.sas_representation_dir

            if os.path.exists(sas_path) and os.path.isfile(sas_path):
                output_directory = self.execute_command_with_runsolver(fd_command, None, sas_path, 1.0)

                with open("%s/cmd.stdout" % (output_directory), 'r') as f:
                    output = f.read()

                    probing_features = self.extract_probing_features(output)
                    features.update(probing_features)

                    # make sure at least one non-sentinel value, otherwise obviously not successful
                    for key,value in features.iteritems():
                        if value != self.sentinel_value:
                            successful = True
            else:
                print "ERROR: %s doesn't exist!!" % sas_path
        except Exception as e:
            print "Exception running FD: %s" % (str(e))
        finally:
            shutil.rmtree(output_directory)

        return successful,features

    def extract_probing_features(self, output):
        probing_features = {}

        reasonable_orders_match = re.search("Removed ([0-9]*) reasonable or obedient reasonable orders", output)
        if reasonable_orders_match:
            probing_features['fdProbingReasonableOrdersRemoved'] = reasonable_orders_match.group(1)

        landmarks_match = re.search("Discovered ([0-9]*) landmarks, of which ([0-9]*) are disjunctive and ([0-9]*) are conjunctive", output)
        if landmarks_match:
            landmarks = float(landmarks_match.group(1))
            disjunctive = float(landmarks_match.group(2))
            conjunctive = float(landmarks_match.group(3))

            probing_features['fdProbingLandmarksDiscovered'] = landmarks

            if landmarks > 0:
                probing_features['fdProbingLandmarksPercentageDisjunctive'] = disjunctive/landmarks
                probing_features['fdProbingLandmarksPercentageConjunctive'] = conjunctive/landmarks

        edges_match = re.search("([0-9]*) edges", output)
        if edges_match:
            probing_features['fdProbingNumEdges'] = edges_match.group(1)

        initial_goal_landmarks_match = re.search("([0-9]*) initial landmarks, ([0-9]*) goal landmarks", output)
        if initial_goal_landmarks_match:
            initial_landmarks = float(initial_goal_landmarks_match.group(1))
            goal_landmarks = float(initial_goal_landmarks_match.group(2))

            probing_features['fdProbingInitialLandmarks'] = initial_landmarks
            probing_features['fdProbingGoalLandmarks'] = goal_landmarks

            if initial_landmarks > 0:
                probing_features['fdProbingRatioGoalLandmarksOverInitialLandmarks'] = goal_landmarks/initial_landmarks


        heuristic_value_pattern = "Best heuristic value: ([0-9]*)\/([0-9]*) \[g=([0-9]*), ([0-9]*) evaluated"

        first = True
        initial_heuristic_num = None
        initial_heuristic_den = None
        initial_heuristic_g = None

        final_heuristic_num = None
        final_heuristic_den = None
        final_heuristic_g = None
        final_states_evaluated = None

        for heuristic_match in re.finditer(heuristic_value_pattern, output):
            num = float(heuristic_match.group(1))
            den = float(heuristic_match.group(2))

            g = float(heuristic_match.group(3))
            evaluated = float(heuristic_match.group(4))

            if first:
                initial_heuristic_num = num
                initial_heuristic_den = den
                initial_heuristic_g = g

                first = False
            else:
                final_heuristic_num = num
                final_heuristic_den = den
                final_heuristic_g = g
                final_states_evaluated = evaluated

        if initial_heuristic_num != None:
            probing_features['fdProbingInitialHeuristicNum'] = initial_heuristic_num
            probing_features['fdProbingInitialHeuristicDen'] = initial_heuristic_den
            probing_features['fdProbingInitialGValue'] = initial_heuristic_g

        if final_heuristic_num != None:
            probing_features['fdProbingFinalHeuristicNum'] = final_heuristic_num
            probing_features['fdProbingFinalHeuristicDen'] = final_heuristic_den
            probing_features['fdProbingFinalHeuristicGValue'] = final_heuristic_g

            probing_features['fdProbingFinalStatesEvaluated'] = final_states_evaluated

            if initial_heuristic_num > 0:
                probing_features['fdProbingPercentageImprovementNum'] = 1.0 - (initial_heuristic_num-final_heuristic_num)/initial_heuristic_num

        return probing_features
