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

import os
import sys
from feature_extractor import FeatureExtractor
from subprocess import Popen, PIPE
import shutil
import re
import math

class SASFeatureExtractor(FeatureExtractor):
    def __init__(self, args):
        super(SASFeatureExtractor, self).__init__(args)

        self.extractor_name = "sas"

        self.sas_graph_features = args.sas_graph_features
        self.creates_sas_representation = True

    def default_features(self):
        base_features = [
            'sasRules',
            'sasRelevantAtoms',
            'sasAuxiliaryAtoms',
            'sasFinalQueueLength',
            'sasTotalQueuePushes',
            'sasInitialInvariantCandidates',
            'sasUncoveredFacts',
            'sasImpliedEffectsRemoved',
            'sasEffectConditionsSimplified',
            'sasImpliedPreconditionsAdded',
            'sasOperatorsRemoved',
            'sasPropositionsRemoved',
            'sasTranslatorVariables',
            'sasTranslatorDerivedVariables',
            'sasTranslatorFacts',
            'sasTranslatorMutexGroups',
            'sasTranslatorTotalMutexGroupsSize',
            'sasTranslatorOperators',
            'sasTranslatorTaskSize',
        ]

        sas_file_features = [
            'sasFileNumVariables',
            'sasFileMinVariableDomainSize',
            'sasFileMeanVariableDomainSize',
            'sasFileMaxVariableDomainSize',
            'sasFileNumGoalPairs',
            'sasFileRatioGoalPairsOverNumVariables',
            'sasFileNumOperators',
            'sasFileMinPrevailConditionsPerOperator',
            'sasFileMeanPrevailConditionsPerOperator',
            'sasFileMaxPrevailConditionsPerOperator',
            'sasFileMinEffectsPerOperator',
            'sasFileMeanEffectsPerOperator',
            'sasFileMaxEffectsPerOperator',
            'sasFileNumAxioms',
            'sasFileMinConditionsPerAxiom',
            'sasFileMeanConditionsPerAxiom',
            'sasFileMaxConditionsPerAxiom',
        ]

        preprocessing_features = [
            'sasPreprocessingPercentageVariablesDeemedNecessary',
            'sasPreprocessingPercentageMutexGroupsDeemedNecessary',
            'sasPreprocessingPercentageOperatorsDeemedNecessary',
            'sasPreprocessingPercentageAxiomRulesDeemedNecessary',
            'sasPreprocessingDeemedPolytimeSolvable',
            'sasPreprocessingNumFacts',
            'sasPreprocessingDerivedVariables',
            'sasPreprocessingTaskSize',
        ]

        graph_features = [
            'sasCenamorTotalNumVariables',
            'sasCenamorNumHighLevelVariables',

            'sasCenamorDTGTotalNumberOfVertices',
            'sasCenamorDTGTotalNumberOfEdges',
            'sasCenamorDTGSumOfEdgeWeights',

            'sasCenamorDTGMaxIncomingEdgesPerVertex',
            'sasCenamorDTGMeanIncomingEdgesPerVertex',
            'sasCenamorDTGStddevIncomingEdgesPerVertex',

            'sasCenamorDTGMaxOutgoingEdgesPerVertex',
            'sasCenamorDTGMeanOutgoingEdgesPerVertex',
            'sasCenamorDTGStddevOutgoingEdgesPerVertex',

            'sasCenamorDTGMaxIncomingEdgeWeightSumPerVertex',
            'sasCenamorDTGMeanIncomingEdgeWeightSumPerVertex',
            'sasCenamorDTGStddevIncomingEdgeWeightSumPerVertex',

            'sasCenamorDTGMaxOutgoingEdgeWeightSumPerVertex',
            'sasCenamorDTGMeanOutgoingEdgeWeightSumPerVertex',
            'sasCenamorDTGStddevOutgoingEdgeWeightSumPerVertex',

            'sasCenamorCGNumEdges',
            'sasCenamorCGSumOfEdgeWeights',

            'sasCenamorCGRatioTotalVariablesToTotalEdges',
            'sasCenamorCGRatioSumOfWeightsToTotalEdges',

            'sasCenamorCGRatioNumHighLevelToTotalVariables',
            'sasCenamorCGRatioSumOfWeightsToTotalVariables',

            'sasCenamorCGMaxIncomingEdgesPerVariable',
            'sasCenamorCGMeanIncomingEdgesPerVariable',
            'sasCenamorCGStddevIncomingEdgesPerVariable',

            'sasCenamorCGMaxOutgoingEdgesPerVariable',
            'sasCenamorCGMeanOutgoingEdgesPerVariable',
            'sasCenamorCGStddevOutgoingEdgesPerVariable',

            'sasCenamorCGMaxIncomingEdgeWeightSumPerVariable',
            'sasCenamorCGMeanIncomingEdgeWeightSumPerVariable',
            'sasCenamorCGStddevIncomingEdgeWeightSumPerVariable',

            'sasCenamorCGMaxOutgoingEdgeWeightSumPerVariable',
            'sasCenamorCGMeanOutgoingEdgeWeightSumPerVariable',
            'sasCenamorCGStddevOutgoingEdgeWeightSumPerVariable',

            'sasCenamorCGMaxIncomingEdgesPerHighLevelVariable',
            'sasCenamorCGMeanIncomingEdgesPerHighLevelVariable',
            'sasCenamorCGStddevIncomingEdgesPerHighLevelVariable',

            'sasCenamorCGMaxIncomingEdgeWeightSumPerHighLevelVariable',
            'sasCenamorCGMeanIncomingEdgeWeightSumPerHighLevelVariable',
            'sasCenamorCGStddevIncomingEdgeWeightSumPerHighLevelVariable',
        ]

        defaults = { key : self.sentinel_value for key in base_features }
        defaults.update({ key : self.sentinel_value for key in sas_file_features })
        defaults.update({ key : self.sentinel_value for key in preprocessing_features })

        if self.sas_graph_features:
            remaining = { key : self.sentinel_value for key in graph_features }
            defaults.update(remaining)

        return defaults

    def extract(self, domain_path, instance_path):
        features = self.default_features()

        path_to_translate = "%s/fast-downward/translate/translate.py" % (self.abs_script_directory)

        translate_cmd = ["python", path_to_translate, domain_path, instance_path]

        successful = False

        try:
            output_directory = self.execute_command_with_runsolver(translate_cmd, None, None)

            with open("%s/cmd.stdout" % (output_directory), 'r') as f:
                output = f.read()

                translate_stdout_features = self.extract_stdout_features(output)
                features.update(translate_stdout_features)

            sas_path = "%s/output.sas" % (output_directory)
            if os.path.exists(sas_path) and os.path.isfile(sas_path):
                sas_file_features = self.extract_sas_file_features(sas_path)
                features.update(sas_file_features)

                # extract the preprocessing features
                path_to_preprocess = "%s/fast-downward/preprocess/preprocess" % (self.abs_script_directory)
                self.execute_command_with_runsolver([path_to_preprocess], output_directory, sas_path)

                with open("%s/cmd.stdout" % (output_directory), 'r') as f:
                    preprocess_output = f.read()

                    preprocess_stdout_features = self.extract_preprocess_stdout_features(preprocess_output)
                    features.update(preprocess_stdout_features)

                    if self.sas_graph_features:
                        preprocessed_path = "%s/output" % (output_directory)
                        if os.path.exists(preprocessed_path) and os.path.isfile(preprocessed_path):
                            sas_graph_features = self.extract_sas_graph_features(preprocessed_path)
                            features.update(sas_graph_features)

                    # make sure at least one non-sentinel value, otherwise obviously not successful
                    for key,value in features.iteritems():
                        if value != self.sentinel_value:
                            successful = True

        except Exception as e:
            print "Exception in parse: %s" % (str(e))
        finally:
            self.sas_representation_dir = output_directory

        return successful,features

    def extract_stdout_features(self, output):
        stdout_features = {}

        sas_rules_match = re.search("Generated ([0-9]*) rules\.", output)
        sas_relevant_atoms_match = re.search("([0-9]*) relevant atoms", output)
        sas_auxiliary_atoms_match = re.search("([0-9]*) auxiliary atoms", output)
        sas_final_queue_length_match = re.search("([0-9]*) final queue length", output)
        sas_total_queue_pushes_match = re.search("([0-9]*) total queue pushes", output)
        sas_initial_invariant_candidates_match = re.search("([0-9]*) initial candidates", output)
        sas_uncovered_facts_match = re.search("([0-9]*) uncovered facts", output)
        sas_implied_effects_removed_match = re.search("([0-9]*) implied effects removed", output)
        sas_effect_conditions_simplified_match = re.search("([0-9]*) effect conditions simplified", output)
        sas_implied_preconditions_added_match = re.search("([0-9]*) implied preconditions added", output)
        sas_operators_removed_match = re.search("([0-9]*) operators removed", output)
        sas_propositions_removed_match = re.search("([0-9]*) propositions removed", output)
        sas_translator_variables_match = re.search("Translator variables: ([0-9]*)", output)
        sas_translator_derived_variables_match = re.search("Translator derived variables: ([0-9]*)", output)
        sas_translator_facts_match = re.search("Translator facts: ([0-9]*)", output)
        sas_translator_mutex_groups_match = re.search("Translator mutex groups: ([0-9]*)", output)
        sas_translator_total_mutex_groups_match = re.search("Translator total mutex groups size: ([0-9]*)", output)
        sas_translator_operators_match = re.search("Translator operators: ([0-9]*)", output)
        sas_translator_task_size_match = re.search("Translator task size: ([0-9]*)", output)

        if sas_rules_match:
            stdout_features['sasRules'] = sas_rules_match.group(1)

        if sas_relevant_atoms_match:
            stdout_features['sasRelevantAtoms'] = sas_relevant_atoms_match.group(1)

        if sas_auxiliary_atoms_match:
            stdout_features['sasAuxiliaryAtoms'] = sas_auxiliary_atoms_match.group(1)

        if sas_final_queue_length_match:
            stdout_features['sasFinalQueueLength'] = sas_final_queue_length_match.group(1)

        if sas_total_queue_pushes_match:
            stdout_features['sasTotalQueuePushes'] = sas_total_queue_pushes_match.group(1)

        if sas_initial_invariant_candidates_match:
            stdout_features['sasInitialInvariantCandidates'] = sas_initial_invariant_candidates_match.group(1)

        if sas_uncovered_facts_match:
            stdout_features['sasUncoveredFacts'] = sas_uncovered_facts_match.group(1)

        if sas_implied_effects_removed_match:
            stdout_features['sasImpliedEffectsRemoved'] = sas_implied_effects_removed_match.group(1)

        if sas_effect_conditions_simplified_match:
            stdout_features['sasEffectConditionsSimplified'] = sas_effect_conditions_simplified_match.group(1)

        if sas_implied_preconditions_added_match:
            stdout_features['sasImpliedPreconditionsAdded'] = sas_implied_preconditions_added_match.group(1)

        if sas_operators_removed_match:
            stdout_features['sasOperatorsRemoved'] = sas_operators_removed_match.group(1)

        if sas_propositions_removed_match:
            stdout_features['sasPropositionsRemoved'] = sas_propositions_removed_match.group(1)

        if sas_translator_variables_match:
            stdout_features['sasTranslatorVariables'] = sas_translator_variables_match.group(1)

        if sas_translator_derived_variables_match:
            stdout_features['sasTranslatorDerivedVariables'] = sas_translator_derived_variables_match.group(1)

        if sas_translator_facts_match:
            stdout_features['sasTranslatorFacts'] = sas_translator_facts_match.group(1)

        if sas_translator_mutex_groups_match:
            stdout_features['sasTranslatorMutexGroups'] = sas_translator_mutex_groups_match.group(1)

        if sas_translator_total_mutex_groups_match:
            stdout_features['sasTranslatorTotalMutexGroupsSize'] = sas_translator_total_mutex_groups_match.group(1)

        if sas_translator_operators_match:
            stdout_features['sasTranslatorOperators'] = sas_translator_operators_match.group(1)

        if sas_translator_task_size_match:
            stdout_features['sasTranslatorTaskSize'] = sas_translator_task_size_match.group(1)

        return stdout_features

    def extract_sas_file_features(self, sas_file):
        sas_features = {}

        with open(sas_file, 'r') as f:
            # begin_metric
            line = f.readline().lstrip().rstrip()
            if line != "begin_version":
                return sas_features

            version = f.readline().lstrip().rstrip()
            if version and len(version) > 0:
                sas_features['sasFileVersion'] = version

            line = f.readline()
            # end_version

            # begin_metric
            line = f.readline().lstrip().rstrip()
            if line != "begin_metric":
                return sas_features

            metric = f.readline().lstrip().rstrip()
            if metric and len(metric) > 0:
                sas_features['sasFileHasMetric'] = metric

            line = f.readline()
            # end_metric

            # number of variables
            line = f.readline().lstrip().rstrip()
            num_variables_match = re.search("^([0-9]*)$", line)
            num_variables = -1
            if num_variables_match:
                num_variables = int(num_variables_match.group(1))

            # read all variables
            variables = []
            for _1 in range(num_variables):
                # begin_variable
                line = f.readline().lstrip().rstrip()
                if line != "begin_variable":
                    print "ERROR: Expected begin_variable but got %s" % (line)
                    return sas_features

                variable_name = f.readline().lstrip().rstrip()
                axiom_layer = int(f.readline().lstrip().rstrip())
                domain_size = int(f.readline().lstrip().rstrip())

                # eat the domain info
                for _2 in range(domain_size):
                    f.readline()

                variables.append([variable_name, axiom_layer, domain_size])

                line = f.readline()
                # end_variable

            # read all mutex groups
            line = f.readline().lstrip().rstrip()
            num_mutex_groups_match = re.search("^([0-9]*)$", line)
            num_mutex_groups = -1
            if num_mutex_groups_match:
                num_mutex_groups = int(num_mutex_groups_match.group(1))

            mutex_groups = []
            for _1 in range(num_mutex_groups):
                line = f.readline().lstrip().rstrip()
                if line != "begin_mutex_group":
                    print "ERROR: Expected begin_mutex_group but got %s" % (line)
                    return sas_features

                num_entries_in_group = int(f.readline().lstrip().rstrip())

                group = []
                for _2 in range(num_entries_in_group):
                    line = f.readline().lstrip().rstrip()
                    mutex_pair_match = re.search("^([0-9]*) ([0-9]*)$", line)
                    if not mutex_pair_match:
                        print "ERROR: Poorly formed mutex pair"
                        return sas_features
                    else:
                        first = int(mutex_pair_match.group(1))
                        second = int(mutex_pair_match.group(2))

                        group.append([first, second])

                mutex_groups.append(group)

                line = f.readline()
                # end_mutex_group

            # begin_state
            line = f.readline().lstrip().rstrip()
            if line != "begin_state":
                print "ERROR: Expected begin_state but got %s" % (line)
                return sas_features

            initial_state = []
            for _1 in range(num_variables):
                val = int(f.readline().lstrip().rstrip())
                initial_state.append(val)

            line = f.readline()
            # end_state

            # begin_goal
            line = f.readline().lstrip().rstrip()
            if line != "begin_goal":
                print "ERROR: Expected begin_goal but got %s" % (line)
                return sas_features

            goal_assignments = []
            num_assignments_in_goal = int(f.readline().lstrip().rstrip())
            for _1 in range(num_assignments_in_goal):
                line = f.readline().lstrip().rstrip()
                pair_match = re.search("^([0-9]*) ([0-9]*)$", line)
                if not pair_match:
                    print "ERROR: Expected goal assignment pair but got %s" % (line)
                    return sas_features

                first = pair_match.group(1)
                second = pair_match.group(2)

                goal_assignments.append([first, second])

            line = f.readline().lstrip().rstrip()
            # end_goal

            # operators
            line = f.readline().lstrip().rstrip()
            num_operators_match = re.search("^([0-9]*)$", line)
            if not num_operators_match:
                print "ERROR: Expected number of operators but got %s" % (line)
                return sas_features

            num_operators = int(num_operators_match.group(1))

            operators = []
            for _1 in range(num_operators):
                line = f.readline().lstrip().rstrip()
                if line != "begin_operator":
                    print "ERROR: Expected begin_operator but got %s" % (line)
                    return sas_features

                operator_name = f.readline().lstrip().rstrip()

                num_prevail_conditions = int(f.readline().lstrip().rstrip())
                prevail_conditions = []
                for _2 in range(num_prevail_conditions):
                    line = f.readline().lstrip().rstrip()
                    pair_match = re.search("^([0-9]*) ([0-9]*)$", line)
                    if not pair_match:
                        print "ERROR: Expected prevail condition pair but got %s" % (line)

                    first = pair_match.group(1)
                    second = pair_match.group(2)

                    prevail_conditions.append([first, second])

                num_effects = int(f.readline().lstrip().rstrip())
                effects = []
                for _2 in range(num_effects):
                    line = f.readline().lstrip().rstrip()
                    effect_nums = line.split(" ")

                    num_conditions = int(effect_nums[0])
                    conditions = []
                    index = 1
                    for _3 in range(num_conditions):
                        first = int(effect_nums[index])
                        second = int(effect_nums[index+1])

                        conditions.append([first,second])
                        index += 2

                    effected_variable = int(effect_nums[index])
                    value_precondition = int(effect_nums[index+1])
                    new_value = int(effect_nums[index+2])

                    effects.append([effected_variable, conditions, value_precondition, new_value])

                operator_cost = float(f.readline().lstrip().rstrip())

                operators.append([operator_name, prevail_conditions, effects, operator_cost])

                line = f.readline().lstrip().rstrip()
                if line != "end_operator":
                    print "ERROR: expected end_operator but got %s" % (line)
                    return sas_features
            # end_operator

            # axiom rules
            line = f.readline().lstrip().rstrip()
            num_rules_match = re.search("^([0-9]*)$", line)
            if not num_rules_match:
                print "ERROR: Expected number of axiom rules but got %s" % (line)
                return sas_features

            num_axiom_rules = int(num_rules_match.group(1))

            axiom_rules = []
            for _1 in range(num_axiom_rules):
                line = f.readline().lstrip().rstrip()
                if line != "begin_rule":
                    print "ERROR: Expected begin_rule but got %s" % (line)
                    return sas_features

                num_conditions = int(f.readline().lstrip().rstrip())
                conditions = []
                for _2 in range(num_conditions):
                    line = f.readline().lstrip().rstrip()
                    pair_match = re.search("^([0-9]*) ([0-9]*)$", line)
                    if not pair_match:
                        print "ERROR: Expected condition pair but got %s" % (line)
                        return sas_features

                    first = pair_match.group(1)
                    second = pair_match.group(2)

                    conditions.append([first, second])

                line = f.readline().lstrip().rstrip()
                triplet_match = re.search("^([0-9]*) ([0-9]*) ([0-9]*)$", line)
                if not triplet_match:
                    print "ERROR: Expected final rule triplet but got %s" % (line)
                    return sas_features

                effected_variable = int(triplet_match.group(1))
                value_precondition = int(triplet_match.group(2))
                new_value = int(triplet_match.group(3))

                axiom_rules.append([effected_variable, conditions, value_precondition, new_value])

                line = f.readline().lstrip().rstrip()
                if line != "end_rule":
                    print "ERROR: Expected end_rule but got %s" % (line)
            # end_rule

            # variable features
            min_variable_domain_size = None
            max_variable_domain_size = None
            total_domain_sizes = 0
            for variable in variables:
                size = variable[2]
                total_domain_sizes += size

                if min_variable_domain_size == None or min_variable_domain_size > size:
                    min_variable_domain_size = size
                if max_variable_domain_size == None or max_variable_domain_size < size:
                    max_variable_domain_size = size

            sas_features['sasFileNumVariables'] = len(variables)
            if len(variables) > 0:
                sas_features['sasFileMinVariableDomainSize'] = min_variable_domain_size
                sas_features['sasFileMeanVariableDomainSize'] = float(total_domain_sizes)/float(len(variables))
                sas_features['sasFileMaxVariableDomainSize'] = max_variable_domain_size

            # goal features
            sas_features['sasFileNumGoalPairs'] = len(goal_assignments)
            if len(variables) > 0:
                sas_features['sasFileRatioGoalPairsOverNumVariables'] = float(len(goal_assignments))/float(len(variables))

            # operator features
            min_prevail_conditions_per_operator = None
            max_prevail_conditions_per_operator = None
            total_prevail_conditions = 0

            min_effects_per_operator = None
            max_effects_per_operator = None
            total_effects = 0

            for operator in operators:
                num_prevail_conditions = len(operator[1])
                num_effects = len(operator[2])

                total_prevail_conditions += num_prevail_conditions
                total_effects += num_effects

                if min_prevail_conditions_per_operator == None or min_prevail_conditions_per_operator > num_prevail_conditions:
                    min_prevail_conditions_per_operator = num_prevail_conditions

                if max_prevail_conditions_per_operator == None or max_prevail_conditions_per_operator < num_prevail_conditions:
                    max_prevail_conditions_per_operator = num_prevail_conditions

                if min_effects_per_operator == None or min_effects_per_operator > num_effects:
                    min_effects_per_operator = num_effects

                if max_effects_per_operator == None or max_effects_per_operator < num_effects:
                    max_effects_per_operator = num_effects

            sas_features['sasFileNumOperators'] = len(operators)

            if len(operators) > 0:
                sas_features['sasFileMinPrevailConditionsPerOperator'] = min_prevail_conditions_per_operator
                sas_features['sasFileMeanPrevailConditionsPerOperator'] = float(total_prevail_conditions)/float(len(operators))
                sas_features['sasFileMaxPrevailConditionsPerOperator'] = max_prevail_conditions_per_operator

                sas_features['sasFileMinEffectsPerOperator'] = min_effects_per_operator
                sas_features['sasFileMeanEffectsPerOperator'] = float(total_effects)/float(len(operators))
                sas_features['sasFileMaxEffectsPerOperator'] = max_effects_per_operator

            # axiom features
            min_conditions_per_axiom = None
            max_conditions_per_axiom = None
            total_axiom_conditions = 0

            for axiom in axiom_rules:
                num_conditions = len(axiom[1])

                total_axiom_conditions += num_conditions

                if min_conditions_per_axiom == None or min_conditions_per_axiom > num_conditions:
                    min_conditions_per_axiom = num_conditions

                if max_conditions_per_axiom == None or max_conditions_per_axiom < num_conditions:
                    max_conditions_per_axiom = num_conditions

            sas_features['sasFileNumAxioms'] = len(axiom_rules)
            if len(axiom_rules) > 0:
                sas_features['sasFileMinConditionsPerAxiom'] = min_conditions_per_axiom
                sas_features['sasFileMeanConditionsPerAxiom'] = float(total_axiom_conditions)/float(len(axiom_rules))
                sas_features['sasFileMaxConditionsPerAxiom'] = max_conditions_per_axiom

        return sas_features

    def extract_preprocess_stdout_features(self, preprocess_output):
        preprocess_stdout_features = {}

        deemed_necessary_match = re.search("([0-9]*) variables of ([0-9]*) necessary", preprocess_output)
        if deemed_necessary_match:
            first = float(deemed_necessary_match.group(1))
            second = float(deemed_necessary_match.group(2))

            if second > 0:
                preprocess_stdout_features['sasPreprocessingPercentageVariablesDeemedNecessary'] = first/second

        mutex_groups_necessary_match = re.search("([0-9]*) of ([0-9]*) mutex groups necessary", preprocess_output)
        if mutex_groups_necessary_match:
            first = float(mutex_groups_necessary_match.group(1))
            second = float(mutex_groups_necessary_match.group(2))

            if second > 0:
                preprocess_stdout_features['sasPreprocessingPercentageMutexGroupsDeemedNecessary'] = first/second

        operators_necessary_match = re.search("([0-9]*) of ([0-9]*) operators necessary", preprocess_output)
        if operators_necessary_match:
            first = float(operators_necessary_match.group(1))
            second = float(operators_necessary_match.group(2))

            if second > 0:
                preprocess_stdout_features['sasPreprocessingPercentageOperatorsDeemedNecessary'] = first/second

        axiom_rules_necessary_match = re.search("([0-9]*) of ([0-9]*) axiom rules necessary", preprocess_output)
        if axiom_rules_necessary_match:
            first = float(axiom_rules_necessary_match.group(1))
            second = float(axiom_rules_necessary_match.group(2))

            if second > 0:
                preprocess_stdout_features['sasPreprocessingPercentageAxiomRulesDeemedNecessary'] = first/second

        polytime_match = re.search("solveable in poly time ([0-9]*)", preprocess_output)
        if polytime_match:
            first = int(polytime_match.group(1))

            preprocess_stdout_features['sasPreprocessingDeemedPolytimeSolvable'] = first

        num_facts_match = re.search("Preprocessor facts: ([0-9]*)", preprocess_output)
        if num_facts_match:
            first = num_facts_match.group(1)

            preprocess_stdout_features['sasPreprocessingNumFacts'] = first

        num_derived_variables_match = re.search("Preprocessor derived variables: ([0-9]*)", preprocess_output)
        if num_derived_variables_match:
            first = num_derived_variables_match.group(1)

            preprocess_stdout_features['sasPreprocessingDerivedVariables'] = first

        task_size_match = re.search("Preprocessor task size: ([0-9]*)", preprocess_output)
        if task_size_match:
            first = task_size_match.group(1)

            preprocess_stdout_features['sasPreprocessingTaskSize'] = first

        return preprocess_stdout_features

    def extract_sas_graph_features(self, preprocessed_path):
        sas_graph_features = {}

        with open(preprocessed_path, 'r') as f:
            # begin_version
            line = f.readline().lstrip().rstrip()
            if line != "begin_version":
                print "ERROR: Expected begin_version but got %s" % (line)
                return sas_graph_features

            version = int(f.readline().lstrip().rstrip())

            line = f.readline().lstrip().rstrip()
            if line != "end_version":
                print "ERROR: Expected end_version but got %s" % (line)
                return sas_graph_features

            # end_version

            # begin_metric
            line = f.readline().lstrip().rstrip()
            if line != "begin_metric":
                print "ERROR: Expected begin_metric but got %s" % (line)
                return sas_graph_features

            metric = int(f.readline().lstrip().rstrip())

            line = f.readline().lstrip().rstrip()
            if line != "end_metric":
                print "ERROR: Expected end_metric but got %s" % (line)
                return sas_graph_features

            # end_metric

            # variables
            line = f.readline().lstrip().rstrip()
            num_variables_match = re.search("^([0-9]*)$", line)
            if not num_variables_match:
                print "ERROR: Expected number of variables but got %s" % (line)
                return sas_graph_features

            num_variables = int(num_variables_match.group(1))

            variables = []
            for _1 in range(num_variables):
                line = f.readline().lstrip().rstrip()
                if line != "begin_variable":
                    print "ERROR: Expected begin_variable but got %s" % (line)
                    return sas_graph_features

                variable_name = f.readline().lstrip().rstrip()
                axiom_layer = int(f.readline().lstrip().rstrip())
                domain_size = int(f.readline().lstrip().rstrip())

                for _2 in range(domain_size):
                    # eat the domain value names
                    f.readline()

                variables.append([variable_name, axiom_layer, domain_size])

                line = f.readline().lstrip().rstrip()
                if line != "end_variable":
                    print "ERROR: Expected end_variable but got %s" % (line)
                    return sas_graph_features

            # end of variables

            # mutex groups
            line = f.readline().lstrip().rstrip()
            num_groups_match = re.search("^([0-9]*)$", line)
            if not num_groups_match:
                print "ERROR: Expected number of mutex groups but got %s" % (line)
                return sas_graph_features

            num_mutex_groups = int(num_groups_match.group(1))

            mutex_groups = []
            for _1 in range(num_mutex_groups):
                line = f.readline().lstrip().rstrip()
                if line != "begin_mutex_group":
                    print "ERROR: Expected begin_mutex_group but got %s" % (line)
                    return sas_graph_features

                num_entries_in_group = int(f.readline().lstrip().rstrip())

                group = []
                for _2 in range(num_entries_in_group):
                    line = f.readline().lstrip().rstrip()
                    pair_match = re.search("^([0-9]*) ([0-9]*)$", line)

                    if not pair_match:
                        print "ERROR: Expected mutex group pair but got %s" % (line)
                        return sas_graph_features

                    first = int(pair_match.group(1))
                    second = int(pair_match.group(2))

                    group.append([first, second])

                mutex_groups.append(group)

                line = f.readline().lstrip().rstrip()
                if line != "end_mutex_group":
                    print "ERROR: Expected end_mutex_group but got %s" % (line)
                    return sas_graph_features

            # end of mutex groups

            # initial state
            line = f.readline().lstrip().rstrip()
            if line != "begin_state":
                print "ERROR: Expected begin_state but got %s" % (line)
                return sas_graph_features

            initial_state = []
            for _1 in range(num_variables):
                val = int(f.readline().lstrip().rstrip())
                initial_state.append(val)

            line = f.readline().lstrip().rstrip()
            if line != "end_state":
                print "ERROR: Expected end_state but got %s" % (line)
                return sas_graph_features

            # end_state

            # goal state
            line = f.readline().lstrip().rstrip()
            if line != "begin_goal":
                print "ERROR: Expected begin_goal but got %s" % (line)
                return sas_graph_features

            goal_variables_set = set()
            goal_assignments = []
            num_assignments_in_goal = int(f.readline().lstrip().rstrip())

            for _1 in range(num_assignments_in_goal):
                line = f.readline().lstrip().rstrip()
                pair_match = re.search("^([0-9]*) ([0-9]*)$", line)

                if not pair_match:
                    print "ERROR: Expected goal assignment pair but got %s" % (line)
                    return sas_graph_features

                first = int(pair_match.group(1))
                second = int(pair_match.group(2))

                goal_assignments.append([first, second])
                goal_variables_set.add(first)

            goal_variables = []
            goal_variables.extend(goal_variables_set)
            goal_variables.sort()

            line = f.readline().lstrip().rstrip()
            if line != "end_goal":
                print "ERROR: Expected end_goal but got %s" % (line)
                return sas_graph_features

            # end_goal

            # operators
            line = f.readline().lstrip().rstrip()
            num_operators_match = re.search("^([0-9]*)$", line)
            if not num_operators_match:
                print "ERROR: Expected number of operators but got %s" % (line)
                return sas_graph_features

            num_operators = int(num_operators_match.group(1))

            operators = []
            for _1 in range(num_operators):
                line = f.readline().lstrip().rstrip()
                if line != "begin_operator":
                    print "ERROR: Expected begin_operator but got %s" % (line)
                    return sas_graph_features

                operator_name = f.readline().lstrip().rstrip()

                num_prevail_conditions = int(f.readline().lstrip().rstrip())

                prevail_conditions = []
                for _2 in range(num_prevail_conditions):
                    line = f.readline().lstrip().rstrip()
                    pair_match = re.search("^([0-9]*) ([0-9]*)$", line)
                    if not pair_match:
                        print "ERROR: Expected prevail condition pair but got %s" % (line)
                        return sas_graph_features

                    first = int(pair_match.group(1))
                    second = int(pair_match.group(2))

                    prevail_conditions.append([first, second])

                num_effects = int(f.readline().lstrip().rstrip())

                effects = []
                for _2 in range(num_effects):
                    line = f.readline().lstrip().rstrip()
                    effect_nums = line.split(" ")

                    num_conditions = int(effect_nums[0])

                    conditions = []
                    index = 1
                    for _3 in range(num_conditions):
                        first = int(effect_nums[index])
                        second = int(effect_nums[index+1])

                        conditions.append([first, second])
                        index += 2

                    effected_variable = int(effect_nums[index])
                    value_precondition = int(effect_nums[index+1])
                    new_value = int(effect_nums[index+1])

                    effects.append([effected_variable, conditions, value_precondition, new_value])

                operator_cost = float(f.readline().lstrip().rstrip())

                operators.append([operator_name, prevail_conditions, effects, operator_cost])

                line = f.readline().lstrip().rstrip()
                if line != "end_operator":
                    print "ERROR: Expected end_operator but got %s" % (line)
                    return sas_graph_features

            # end operators

            # axiom rules
            line = f.readline().lstrip().rstrip()
            num_rules_match = re.search("^([0-9]*)$", line)
            if not num_rules_match:
                print "ERROR: Expected number of axiom rules but got %s" % (line)
                return sas_graph_features

            num_axiom_rules = int(num_rules_match.group(1))

            axiom_rules = []
            for _1 in range(num_axiom_rules):
                line = f.readline().lstrip().rstrip()
                if line != "begin_rule":
                    print "ERROR: Expected begin_rule but got %s" % (line)
                    return sas_graph_features

                num_conditions = int(f.readline().lstrip().rstrip())

                conditions = []

                for _2 in range(num_conditions):
                    line = f.readline().lstrip().rstrip()
                    pair_match = re.search("^([0-9]*) ([0-9]*)$", line)
                    if not pair_match:
                        print "ERROR: Expected condition pair but got %s" % (line)
                        return sas_graph_features

                    first = int(pair_match.group(1))
                    second = int(pair_match.group(2))

                    conditions.append([first, second])

                line = f.readline().lstrip().rstrip()
                triplet_match = re.search("^([0-9]*) ([0-9]*) ([0-9]*)$", line)
                if not triplet_match:
                    print "ERROR: Expected final rule triplet but got %s" % (line)
                    return sas_graph_features

                effected_variable = int(triplet_match.group(1))
                value_precondition = int(triplet_match.group(2))
                new_value = int(triplet_match.group(3))

                axiom_rules.append([effected_variable, conditions, value_precondition, new_value])

                line = f.readline().lstrip().rstrip()
                if line != "end_rule":
                    print "ERROR: Expected end_rule but got %s" % (line)
                    return sas_graph_features

            # end axiom rules

            # SG
            line = f.readline().lstrip().rstrip()
            if line != "begin_SG":
                print "ERROR: Expected begin_SG but got %s" % (line)
                return sas_graph_features

            line = f.readline().lstrip().rstrip()
            while line != "end_SG":
                line = f.readline().lstrip().rstrip()

            # end SG

            dtg_per_variable = {}
            for vindex in range(num_variables):
                line = f.readline().lstrip().rstrip()
                if line != "begin_DTG":
                    print "ERROR: Expected begin_DTG but got %s" % (line)
                    return sas_graph_features

                num_edges = 0
                sum_of_edge_weights = 0
                edges = []
                incoming_edges_per_value = {}
                outgoing_edges_per_value = {}

                domain_size = variables[vindex][2]

                value = 0
                for _1 in range(domain_size):
                    num_transitions = int(f.readline().lstrip().rstrip())

                    outgoing_edges_per_value[value] = []

                    for _2 in range(num_transitions):
                        new_value = int(f.readline().lstrip().rstrip())
                        operator_index = int(f.readline().lstrip().rstrip())

                        precondition_count = int(f.readline().lstrip().rstrip())
                        for _3 in range(precondition_count):
                            line = f.readline().lstrip().rstrip()
                            pair_match = re.search("^([0-9]*) ([0-9]*)$", line)
                            if not pair_match:
                                print "ERROR: DTG %d expected prevail condition <var_index> <value> but got %s" % (vindex, line)
                                return sas_graph_features

                        operator = operators[operator_index]
                        action_cost = operator[3]
                        sum_of_edge_weights += action_cost

                        edge = [value, new_value, action_cost]

                        edges.append(edge)

                        if new_value not in incoming_edges_per_value:
                            incoming_edges_per_value[new_value] = []

                        incoming_edges_per_value[new_value].append(num_edges)
                        outgoing_edges_per_value[value].append(num_edges)

                        num_edges += 1

                    value += 1

                dtg_per_variable[vindex] = [edges, incoming_edges_per_value, outgoing_edges_per_value, sum_of_edge_weights]

                line = f.readline().lstrip().rstrip()
                while line != "end_DTG":
                    print "ERROR: DTG %d - eating additional line %s" % (vindex, line)
                    line = f.readline().lstrip().rstrip()
            # end DTG

            # DTG statistics
            dtg_total_number_of_vertices = 0.0
            dtg_total_number_of_edges = 0.0
            dtg_sum_of_edge_weights = 0.0

            for vindex,value in dtg_per_variable.iteritems():
                dtg_total_number_of_vertices += len(value[2])
                dtg_total_number_of_edges += len(value[0])
                dtg_sum_of_edge_weights += value[3]

            dtg_max_incoming_edges_per_vertex = None
            dtg_mean_incoming_edges_per_vertex = None
            dtg_total_incoming_edges_per_vertex = 0.0

            dtg_max_outgoing_edges_per_vertex = None
            dtg_mean_outgoing_edges_per_vertex = None
            dtg_total_outgoing_edges_per_vertex = 0.0

            dtg_max_incoming_edge_weight_sum_per_vertex = None
            dtg_mean_incoming_edge_weight_sum_per_vertex = None
            dtg_total_incoming_edge_weight_sum_per_vertex = 0.0

            dtg_max_outgoing_edge_weight_sum_per_vertex = None
            dtg_mean_outgoing_edge_weight_sum_per_vertex = None
            dtg_total_outgoing_edge_weight_sum_per_vertex = 0.0

            dtg_total_vertices = 0.0

            for vindex,value in dtg_per_variable.iteritems():
                edges = value[0]
                incoming = value[1]
                outgoing = value[2]

                dtg_total_vertices += len(outgoing)

                sum_of_incoming_edge_weights = 0.0
                for val_index,inc_edges in incoming.iteritems():
                    num_incoming = len(inc_edges)

                    inc_weights = 0.0
                    for index in inc_edges:
                        e = edges[index]
                        inc_weights += e[2]

                    dtg_total_incoming_edges_per_vertex += num_incoming
                    sum_of_incoming_edge_weights += inc_weights

                    if dtg_max_incoming_edges_per_vertex == None or dtg_max_incoming_edges_per_vertex < num_incoming:
                        dtg_max_incoming_edges_per_vertex = num_incoming

                    if dtg_max_incoming_edge_weight_sum_per_vertex == None or dtg_max_incoming_edge_weight_sum_per_vertex < inc_weights:
                        dtg_max_incoming_edge_weight_sum_per_vertex = inc_weights

                sum_of_outgoing_edge_weights = 0.0
                for val_index,out_edges in outgoing.iteritems():
                    num_outgoing = len(out_edges)

                    out_weights = 0.0
                    for index in out_edges:
                        e = edges[index]
                        out_weights += e[2]

                    dtg_total_outgoing_edges_per_vertex += num_outgoing
                    sum_of_outgoing_edge_weights += out_weights

                    if dtg_max_outgoing_edges_per_vertex == None or dtg_max_outgoing_edges_per_vertex < num_outgoing:
                        dtg_max_outgoing_edges_per_vertex = num_outgoing

                    if dtg_max_outgoing_edge_weight_sum_per_vertex == None or dtg_max_outgoing_edge_weight_sum_per_vertex < out_weights:
                        dtg_max_outgoing_edge_weight_sum_per_vertex = out_weights

                dtg_total_incoming_edge_weight_sum_per_vertex += sum_of_incoming_edge_weights
                dtg_total_outgoing_edge_weight_sum_per_vertex += sum_of_outgoing_edge_weights

            if dtg_total_vertices > 0:
                dtg_mean_incoming_edges_per_vertex = float(dtg_total_incoming_edges_per_vertex)/float(dtg_total_vertices)
                dtg_mean_outgoing_edges_per_vertex = float(dtg_total_outgoing_edges_per_vertex)/float(dtg_total_vertices)

                dtg_mean_incoming_edge_weight_sum_per_vertex = float(dtg_total_incoming_edge_weight_sum_per_vertex)/float(dtg_total_vertices)
                dtg_mean_outgoing_edge_weight_sum_per_vertex = float(dtg_total_outgoing_edge_weight_sum_per_vertex)/float(dtg_total_vertices)

            dtg_variance_incoming_edges_per_vertex_acc = 0.0
            dtg_variance_outgoing_edges_per_vertex_acc = 0.0
            dtg_variance_incoming_edge_weight_sum_per_vertex_acc = 0.0
            dtg_variance_outgoing_edge_weight_sum_per_vertex_acc = 0.0

            for variable,value in dtg_per_variable.iteritems():
                edges = value[0]
                incoming = value[1]
                outgoing = value[2]

                dtg_total_vertices += len(outgoing)

                for val_index,inc_edges in incoming.iteritems():
                    num_incoming = len(inc_edges)

                    inc_weights = 0.0
                    for index in inc_edges:
                        e = edges[index]
                        inc_weights += e[2]

                    foo = num_incoming - dtg_mean_incoming_edges_per_vertex
                    dtg_variance_incoming_edges_per_vertex_acc += foo*foo

                    bar = inc_weights - dtg_mean_incoming_edge_weight_sum_per_vertex
                    dtg_variance_incoming_edge_weight_sum_per_vertex_acc += bar*bar

                sum_of_outgoing_edge_weights = 0.0
                for val_index,out_edges in outgoing.iteritems():
                    num_outgoing = len(out_edges)

                    out_weights = 0.0
                    for index in out_edges:
                        e = edges[index]
                        out_weights += e[2]

                    foo = num_outgoing - dtg_mean_outgoing_edges_per_vertex
                    dtg_variance_outgoing_edges_per_vertex_acc += foo*foo

                    bar = out_weights - dtg_mean_outgoing_edge_weight_sum_per_vertex
                    dtg_variance_outgoing_edge_weight_sum_per_vertex_acc += bar*bar

            dtg_variance_incoming_edges_per_vertex = None
            dtg_variance_outgoing_edges_per_vertex = None
            dtg_variance_incoming_edge_weight_sum_per_vertex = None
            dtg_variance_outgoing_edge_weight_sum_per_vertex = None

            dtg_stddev_incoming_edges_per_vertex = None
            dtg_stddev_outgoing_edges_per_vertex = None
            dtg_stddev_incoming_edge_weight_sum_per_vertex = None
            dtg_stddev_outgoing_edge_weight_sum_per_vertex = None

            if dtg_total_vertices > 1:
                dtg_variance_incoming_edges_per_vertex = float(dtg_variance_incoming_edges_per_vertex_acc)/(dtg_total_vertices-1.0)
                dtg_variance_outgoing_edges_per_vertex = float(dtg_variance_outgoing_edges_per_vertex_acc)/(dtg_total_vertices-1.0)
                dtg_variance_incoming_edge_weight_sum_per_vertex = float(dtg_variance_incoming_edge_weight_sum_per_vertex_acc)/(dtg_total_vertices-1.0)
                dtg_variance_outgoing_edge_weight_sum_per_vertex = float(dtg_variance_outgoing_edge_weight_sum_per_vertex_acc)/(dtg_total_vertices-1.0)

                dtg_stddev_incoming_edges_per_vertex = math.sqrt(dtg_variance_incoming_edges_per_vertex)
                dtg_stddev_outgoing_edges_per_vertex = math.sqrt(dtg_variance_outgoing_edges_per_vertex)
                dtg_stddev_incoming_edge_weight_sum_per_vertex = math.sqrt(dtg_variance_incoming_edge_weight_sum_per_vertex)
                dtg_stddev_outgoing_edge_weight_sum_per_vertex = math.sqrt(dtg_variance_outgoing_edge_weight_sum_per_vertex)

            # handle the 0-incoming and 0-outgoing edges case for these vars
            if dtg_max_incoming_edges_per_vertex == None:
                dtg_max_incoming_edges_per_vertex = 0.0

            if dtg_max_incoming_edge_weight_sum_per_vertex == None:
                dtg_max_incoming_edge_weight_sum_per_vertex = 0.0

            if dtg_max_outgoing_edges_per_vertex == None:
                dtg_max_outgoing_edges_per_vertex = 0.0

            if dtg_max_outgoing_edge_weight_sum_per_vertex == None:
                dtg_max_outgoing_edge_weight_sum_per_vertex = 0.0

            # CG
            line = f.readline().lstrip().rstrip()
            if line != "begin_CG":
                print "ERROR: Expected begin_CG but got %s" % (line)
                return sas_graph_features

            cg_num_edges = 0
            cg_sum_of_edge_weights = 0.0
            cg_edges = []
            cg_incoming_edges_per_variable = {}
            cg_outgoing_edges_per_variable = {}
            for var_index in range(len(variables)):
                num_causal_successors = int(f.readline().lstrip().rstrip())

                if var_index not in cg_outgoing_edges_per_variable:
                    cg_outgoing_edges_per_variable[var_index] = []

                for _1 in range(num_causal_successors):
                    line = f.readline().lstrip().rstrip()

                    pair_match = re.search("^([0-9]*) ([0-9]*)$", line)
                    if not pair_match:
                        print "ERROR: Expected <var_index> <weight> pair but got %s" % (line)
                        return sas_graph_features

                    first = int(pair_match.group(1))
                    second = int(pair_match.group(2))

                    cg_sum_of_edge_weights += second

                    cg_edges.append([var_index, first, second])

                    if first not in cg_incoming_edges_per_variable:
                        cg_incoming_edges_per_variable[first] = []

                    cg_outgoing_edges_per_variable[var_index].append(cg_num_edges)
                    cg_incoming_edges_per_variable[first].append(cg_num_edges)

                    cg_num_edges += 1

            line = f.readline().lstrip().rstrip()
            if line != "end_CG":
                print "ERROR: Expected end_CG but got %s" % (line)
                return sas_graph_features

            # end CG

            # CG statistics
            cg_max_incoming_edges_per_variable = None
            cg_total_incoming_edges_per_variable = 0

            cg_max_outgoing_edges_per_variable = None
            cg_total_outgoing_edges_per_variable = 0

            cg_max_incoming_edge_weight_sum_per_variable = None
            cg_total_incoming_edge_weight_sum_per_variable = 0.0

            cg_max_outgoing_edge_weight_sum_per_variable = None
            cg_total_outgoing_edge_weight_sum_per_variable = 0.0

            for var_index in range(len(variables)):
                if var_index in cg_incoming_edges_per_variable:
                    incoming = cg_incoming_edges_per_variable[var_index]
                else:
                    incoming = []

                if var_index in cg_outgoing_edges_per_variable:
                    outgoing = cg_outgoing_edges_per_variable[var_index]
                else:
                    outgoing = []

                incoming_weight_sum = 0
                for in_edge in incoming:
                    incoming_weight_sum += cg_edges[in_edge][2]

                outgoing_weight_sum = 0
                for out_edge in outgoing:
                    outgoing_weight_sum += cg_edges[out_edge][2]

                cg_total_incoming_edges_per_variable += len(incoming)
                cg_total_outgoing_edges_per_variable += len(outgoing)
                cg_total_incoming_edge_weight_sum_per_variable += incoming_weight_sum
                cg_total_outgoing_edge_weight_sum_per_variable += outgoing_weight_sum

                if cg_max_incoming_edges_per_variable == None or cg_max_incoming_edges_per_variable < len(incoming):
                    cg_max_incoming_edges_per_variable = len(incoming)

                if cg_max_outgoing_edges_per_variable == None or cg_max_outgoing_edges_per_variable < len(outgoing):
                    cg_max_outgoing_edges_per_variable = len(outgoing)

                if cg_max_incoming_edge_weight_sum_per_variable == None or cg_max_incoming_edge_weight_sum_per_variable < incoming_weight_sum:
                    cg_max_incoming_edge_weight_sum_per_variable = incoming_weight_sum

                if cg_max_outgoing_edge_weight_sum_per_variable == None or cg_max_outgoing_edge_weight_sum_per_variable < outgoing_weight_sum:
                    cg_max_outgoing_edge_weight_sum_per_variable = outgoing_weight_sum

            cg_mean_incoming_edges_per_variable = None
            cg_mean_outgoing_edges_per_variable = None
            cg_mean_incoming_edge_weight_sum_per_variable = None
            cg_mean_outgoing_edge_weight_sum_per_variable = None

            if len(variables) > 0:
                cg_mean_incoming_edges_per_variable = float(cg_total_incoming_edges_per_variable)/float(len(variables))
                cg_mean_outgoing_edges_per_variable = float(cg_total_outgoing_edges_per_variable)/float(len(variables))
                cg_mean_incoming_edge_weight_sum_per_variable = float(cg_total_incoming_edge_weight_sum_per_variable)/float(len(variables))
                cg_mean_outgoing_edge_weight_sum_per_variable = float(cg_total_outgoing_edge_weight_sum_per_variable)/float(len(variables))

            cg_max_incoming_edges_per_high_level_variable = None
            cg_total_incoming_edges_per_high_level_variable = 0

            cg_max_incoming_edge_weight_sum_per_high_level_variable = None
            cg_total_incoming_edge_weight_sum_per_high_level_variable = 0

            for var_index in goal_variables:
                if var_index in cg_incoming_edges_per_variable:
                    incoming = cg_incoming_edges_per_variable[var_index]
                else:
                    incoming = []

                incoming_weight_sum = 0.0
                for in_edge in incoming:
                    incoming_weight_sum += cg_edges[in_edge][2]

                cg_total_incoming_edges_per_high_level_variable += len(incoming)
                cg_total_incoming_edge_weight_sum_per_high_level_variable += incoming_weight_sum

                if cg_max_incoming_edges_per_high_level_variable == None or cg_max_incoming_edges_per_high_level_variable < len(incoming):
                    cg_max_incoming_edges_per_high_level_variable = len(incoming)

                if cg_max_incoming_edge_weight_sum_per_high_level_variable == None or cg_max_incoming_edge_weight_sum_per_high_level_variable < incoming_weight_sum:
                    cg_max_incoming_edge_weight_sum_per_high_level_variable = incoming_weight_sum

            cg_mean_incoming_edges_per_high_level_variable = None
            cg_mean_incoming_edge_weight_sum_per_high_level_variable = None
            if len(goal_variables) > 0:
                cg_mean_incoming_edges_per_high_level_variable = float(cg_total_incoming_edges_per_high_level_variable)/float(len(goal_variables))
                cg_mean_incoming_edge_weight_sum_per_high_level_variable = float(cg_total_incoming_edge_weight_sum_per_high_level_variable)/float(len(goal_variables))

            cg_variance_incoming_edges_per_variable_acc = 0.0
            cg_variance_outgoing_edges_per_variable_acc = 0.0
            cg_variance_incoming_edge_weight_sum_per_variable_acc = 0.0
            cg_variance_outgoing_edge_weight_sum_per_variable_acc = 0.0

            for var_index in range(len(variables)):
                if var_index in cg_incoming_edges_per_variable:
                    incoming = cg_incoming_edges_per_variable[var_index]
                else:
                    incoming = []

                if var_index in cg_outgoing_edges_per_variable:
                    outgoing = cg_outgoing_edges_per_variable[var_index]
                else:
                    outgoing = []

                incoming_weight_sum = 0.0
                for in_edge in incoming:
                    incoming_weight_sum += cg_edges[in_edge][2]

                outgoing_weight_sum = 0.0
                for out_edge in outgoing:
                    outgoing_weight_sum += cg_edges[out_edge][2]

                foo = len(incoming) - cg_mean_incoming_edges_per_variable
                cg_variance_incoming_edges_per_variable_acc += foo*foo

                foo = len(outgoing) - cg_mean_outgoing_edges_per_variable
                cg_variance_outgoing_edges_per_variable_acc += foo*foo

                foo = incoming_weight_sum - cg_mean_incoming_edge_weight_sum_per_variable
                cg_variance_incoming_edge_weight_sum_per_variable_acc += foo*foo

                foo = outgoing_weight_sum - cg_mean_outgoing_edge_weight_sum_per_variable
                cg_variance_outgoing_edge_weight_sum_per_variable_acc += foo*foo

            cg_variance_incoming_edges_per_variable = None
            cg_variance_outgoing_edges_per_variable = None
            cg_variance_incoming_edge_weight_sum_per_variable = None
            cg_variance_outgoing_edge_weight_sum_per_variable = None

            cg_stddev_incoming_edges_per_variable = None
            cg_stddev_outgoing_edges_per_variable = None
            cg_stddev_incoming_edge_weight_sum_per_variable = None
            cg_stddev_outgoing_edge_weight_sum_per_variable = None

            if len(variables) > 1:
                cg_variance_incoming_edges_per_variable = float(cg_variance_incoming_edges_per_variable_acc)/float(len(variables)-1.0)
                cg_variance_outgoing_edges_per_variable = float(cg_variance_outgoing_edges_per_variable_acc)/float(len(variables)-1.0)
                cg_variance_incoming_edge_weight_sum_per_variable = float(cg_variance_incoming_edge_weight_sum_per_variable_acc)/float(len(variables)-1.0)
                cg_variance_outgoing_edge_weight_sum_per_variable = float(cg_variance_outgoing_edge_weight_sum_per_variable_acc)/float(len(variables)-1.0)

                cg_stddev_incoming_edges_per_variable = math.sqrt(cg_variance_incoming_edges_per_variable)
                cg_stddev_outgoing_edges_per_variable = math.sqrt(cg_variance_outgoing_edges_per_variable)
                cg_stddev_incoming_edge_weight_sum_per_variable = math.sqrt(cg_variance_incoming_edge_weight_sum_per_variable)
                cg_stddev_outgoing_edge_weight_sum_per_variable = math.sqrt(cg_variance_outgoing_edge_weight_sum_per_variable)


            cg_variance_incoming_edges_per_high_level_variable_acc = 0.0
            cg_variance_incoming_edge_weight_sum_per_high_level_variable_acc = 0.0

            for var_index in goal_variables:
                if var_index in cg_incoming_edges_per_variable:
                    incoming = cg_incoming_edges_per_variable[var_index]
                else:
                    incoming = []

                incoming_weight_sum = 0.0
                for in_edge in incoming:
                    incoming_weight_sum += cg_edges[in_edge][2]

                foo = len(incoming) - cg_mean_incoming_edges_per_high_level_variable
                cg_variance_incoming_edges_per_high_level_variable_acc += foo*foo

                foo = incoming_weight_sum - cg_mean_incoming_edge_weight_sum_per_high_level_variable
                cg_variance_incoming_edge_weight_sum_per_high_level_variable_acc += foo*foo

            cg_variance_incoming_edges_per_high_level_variable = None
            cg_variance_incoming_edge_weight_sum_per_high_level_variable = None
            cg_stddev_incoming_edges_per_high_level_variable = None
            cg_stddev_incoming_edge_weight_sum_per_high_level_variable = None

            if len(goal_variables) > 1:
                cg_variance_incoming_edges_per_high_level_variable = float(cg_variance_incoming_edges_per_high_level_variable_acc)/float(len(goal_variables)-1.0)
                cg_variance_incoming_edge_weight_sum_per_high_level_variable = float(cg_variance_incoming_edge_weight_sum_per_high_level_variable_acc)/float(len(goal_variables)-1.0)

                cg_stddev_incoming_edges_per_high_level_variable = math.sqrt(cg_variance_incoming_edges_per_high_level_variable)
                cg_stddev_incoming_edge_weight_sum_per_high_level_variable = math.sqrt(cg_variance_incoming_edge_weight_sum_per_high_level_variable)

            # end CG statistics

            sas_graph_features['sasCenamorTotalNumVariables'] = len(variables)
            sas_graph_features['sasCenamorNumHighLevelVariables'] = len(goal_variables)

            # DTG

            sas_graph_features['sasCenamorDTGTotalNumberOfVertices'] = dtg_total_number_of_vertices
            sas_graph_features['sasCenamorDTGTotalNumberOfEdges'] = dtg_total_number_of_edges
            sas_graph_features['sasCenamorDTGSumOfEdgeWeights'] = dtg_sum_of_edge_weights

            if dtg_total_vertices > 0:
                sas_graph_features['sasCenamorDTGMaxIncomingEdgesPerVertex'] = dtg_max_incoming_edges_per_vertex
                sas_graph_features['sasCenamorDTGMeanIncomingEdgesPerVertex'] = dtg_mean_incoming_edges_per_vertex
                sas_graph_features['sasCenamorDTGStddevIncomingEdgesPerVertex'] = dtg_stddev_incoming_edges_per_vertex

                sas_graph_features['sasCenamorDTGMaxOutgoingEdgesPerVertex'] = dtg_max_outgoing_edges_per_vertex
                sas_graph_features['sasCenamorDTGMeanOutgoingEdgesPerVertex'] = dtg_mean_outgoing_edges_per_vertex
                sas_graph_features['sasCenamorDTGStddevOutgoingEdgesPerVertex'] = dtg_stddev_outgoing_edges_per_vertex

                sas_graph_features['sasCenamorDTGMaxIncomingEdgeWeightSumPerVertex'] = dtg_max_incoming_edge_weight_sum_per_vertex
                sas_graph_features['sasCenamorDTGMeanIncomingEdgeWeightSumPerVertex'] = dtg_mean_incoming_edge_weight_sum_per_vertex
                sas_graph_features['sasCenamorDTGStddevIncomingEdgeWeightSumPerVertex'] = dtg_stddev_incoming_edge_weight_sum_per_vertex

                sas_graph_features['sasCenamorDTGMaxOutgoingEdgeWeightSumPerVertex'] = dtg_max_outgoing_edge_weight_sum_per_vertex
                sas_graph_features['sasCenamorDTGMeanOutgoingEdgeWeightSumPerVertex'] = dtg_mean_outgoing_edge_weight_sum_per_vertex
                sas_graph_features['sasCenamorDTGStddevOutgoingEdgeWeightSumPerVertex']= dtg_stddev_outgoing_edge_weight_sum_per_vertex

            # CG

            sas_graph_features['sasCenamorCGNumEdges'] = len(cg_edges)
            sas_graph_features['sasCenamorCGSumOfEdgeWeights'] = cg_sum_of_edge_weights

            if len(cg_edges) > 0:
                sas_graph_features['sasCenamorCGRatioTotalVariablesToTotalEdges'] = float(len(variables))/float(len(cg_edges))
                sas_graph_features['sasCenamorCGRatioSumOfWeightsToTotalEdges'] = float(cg_sum_of_edge_weights)/float(len(cg_edges))

            if len(variables) > 0:
                sas_graph_features['sasCenamorCGRatioNumHighLevelToTotalVariables'] = float(len(goal_variables))/float(len(variables))
                sas_graph_features['sasCenamorCGRatioSumOfWeightsToTotalVariables'] = float(cg_sum_of_edge_weights)/float(len(variables))

                sas_graph_features['sasCenamorCGMaxIncomingEdgesPerVariable'] = cg_max_incoming_edges_per_variable
                sas_graph_features['sasCenamorCGMeanIncomingEdgesPerVariable'] = cg_mean_incoming_edges_per_variable

                sas_graph_features['sasCenamorCGMaxOutgoingEdgesPerVariable'] = cg_max_outgoing_edges_per_variable
                sas_graph_features['sasCenamorCGMeanOutgoingEdgesPerVariable'] = cg_mean_outgoing_edges_per_variable

                sas_graph_features['sasCenamorCGMaxIncomingEdgeWeightSumPerVariable'] = cg_max_incoming_edge_weight_sum_per_variable
                sas_graph_features['sasCenamorCGMeanIncomingEdgeWeightSumPerVariable'] = cg_mean_incoming_edge_weight_sum_per_variable

                sas_graph_features['sasCenamorCGMaxOutgoingEdgeWeightSumPerVariable'] = cg_max_outgoing_edge_weight_sum_per_variable
                sas_graph_features['sasCenamorCGMeanOutgoingEdgeWeightSumPerVariable'] = cg_mean_outgoing_edge_weight_sum_per_variable

                if len(variables) > 1:
                    sas_graph_features['sasCenamorCGStddevIncomingEdgesPerVariable'] = cg_stddev_incoming_edges_per_variable
                    sas_graph_features['sasCenamorCGStddevOutgoingEdgesPerVariable'] = cg_stddev_outgoing_edges_per_variable
                    sas_graph_features['sasCenamorCGStddevIncomingEdgeWeightSumPerVariable'] = cg_stddev_incoming_edge_weight_sum_per_variable
                    sas_graph_features['sasCenamorCGStddevOutgoingEdgeWeightSumPerVariable'] = cg_stddev_outgoing_edge_weight_sum_per_variable

            if len(goal_variables) > 0:
                sas_graph_features['sasCenamorCGMaxIncomingEdgesPerHighLevelVariable'] = cg_max_incoming_edges_per_high_level_variable
                sas_graph_features['sasCenamorCGMeanIncomingEdgesPerHighLevelVariable'] = cg_mean_incoming_edges_per_high_level_variable

                sas_graph_features['sasCenamorCGMaxIncomingEdgeWeightSumPerHighLevelVariable'] = cg_max_incoming_edge_weight_sum_per_high_level_variable
                sas_graph_features['sasCenamorCGMeanIncomingEdgeWeightSumPerHighLevelVariable'] = cg_mean_incoming_edge_weight_sum_per_high_level_variable

                if len(goal_variables) > 1:
                    sas_graph_features['sasCenamorCGStddevIncomingEdgesPerHighLevelVariable'] = cg_stddev_incoming_edges_per_high_level_variable
                    sas_graph_features['sasCenamorCGStddevIncomingEdgeWeightSumPerHighLevelVariable'] = cg_stddev_incoming_edge_weight_sum_per_high_level_variable

        return sas_graph_features
