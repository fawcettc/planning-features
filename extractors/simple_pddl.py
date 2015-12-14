#!/usr/bin/env python2.7
# encoding: utf-8

from feature_extractor import FeatureExtractor

import pddl
from pddl import conditions
from pddl import f_expression

class SimplePDDLFeatureExtractor(FeatureExtractor):
    def __init__(self, args):
        super(SimplePDDLFeatureExtractor, self).__init__(args)

        self.extractor_name = "simple-pddl"
        self.simple_pddl_extended_features = args.simple_pddl_extended_features

    def default_features(self):
        base_features = [
            'pddlNumActions',
            'pddlNumPredicates',

            'pddlMinParamsPerPredicate',
            'pddlMeanParamsPerPredicate',
            'pddlMaxParamsPerPredicate',

            'pddlMinPredicatesPerPrecondition',
            'pddlMeanPredicatesPerPrecondition',
            'pddlMaxPredicatesPerPrecondition',

            'pddlMinPredicatesPerEffect',
            'pddlMeanPredicatesPerEffect',
            'pddlMaxPredicatesPerEffect',

            'pddlMinNegationsPerEffect',
            'pddlMeanNegationsPerEffect',
            'pddlMaxNegationsPerEffect',

            'pddlMarksTotalNumActions',
            'pddlRatioActionsWithNegativeEffectsOverActions',

            'pddlNumGoals',
            'pddlNumObjects',

            'pddlNumInitialConditions',

            'pddlRequiresADL',
            'pddlRequiresConditionalEffects',
            'pddlRequiresDerivedPredicates',
            'pddlRequiresDisjunctivePreconditions',
            'pddlRequiresDomainAxioms',
            'pddlRequiresEquality',
            'pddlRequiresExistentialPreconditions',
            'pddlRequiresFluents',
            'pddlRequiresQuantifiedPreconditions',
            'pddlRequiresSafetyConstraints',
            'pddlRequiresStrips',
            'pddlRequiresTyping',
            'pddlRequiresUniversalPreconditions',
        ]

        extended_features = [
            'pddlNumConstants',
            'pddlNumConstantsAndObjects',

            'pddlNumEqualityInitialConditions',
            'pddlNumFunctionAssignmentsInInitialConditions',

            'pddlHasTypes',
            'pddlNumTypes',

            'pddlRequiresActionCosts',
            'pddlRequiresNegation',
            'pddlRequiresNegativePreconditions',
            'pddlRequiresNumericFluents',
            'pddlRequiresObjectFluents',
            'pddlRequiresDurativeActions',
            'pddlRequiresDurationInequalities',
            'pddlRequiresContinuousEffects',
            'pddlRequiresTimedInitialLiterals',
            'pddlRequiresPreferences',
            'pddlRequiresConstraints',
        ]

        defaults = { key : self.sentinel_value for key in base_features }

        if self.simple_pddl_extended_features:
            remaining = { key : self.sentinel_value for key in extended_features }
            defaults.update(remaining)

        return defaults

    def extract(self, domain_path, instance_path):
        features = self.default_features()

        successful = False

        try:
            task = pddl.open(task_filename=instance_path, domain_filename=domain_path)

            pddl_features = self.extract_features_from_pddl_task(task)
            features.update(pddl_features)

            # make sure at least one non-sentinel value, otherwise obviously not successful
            for key,value in features.iteritems():
                if value != self.sentinel_value:
                    successful = True
        except Exception as e:
            print "Exception running simple_pddl extraction: %s" % (str(e))

        return successful,features

    def extract_features_from_pddl_task(self, task):
        pddl_features = {}

        num_actions = len(task.actions)

        # length-1 because we don't want to count the equality predicate
        num_predicates = len(task.predicates)-1

        pddl_features['pddlNumActions'] = num_actions
        pddl_features['pddlNumPredicates'] = num_predicates

        # predicate arity (min, mean, max)
        if num_predicates > 0:
            total_params = 0.0
            min_params_per_predicate = None
            max_params_per_predicate = None

            for predicate in task.predicates:
                if predicate.name != '=':
                    num_arguments = len(predicate.arguments)
                    total_params += num_arguments

                    if min_params_per_predicate == None or min_params_per_predicate > num_arguments:
                        min_params_per_predicate = num_arguments

                    if max_params_per_predicate == None or max_params_per_predicate < num_arguments:
                        max_params_per_predicate = num_arguments

            if num_predicates > 0:
                pddl_features['pddlMinParamsPerPredicate'] = min_params_per_predicate
                pddl_features['pddlMeanParamsPerPredicate'] = float(total_params)/float(num_predicates)
                pddl_features['pddlMaxParamsPerPredicate'] = max_params_per_predicate

        # predicates in preconditions (min, mean, max)
        if num_actions > 0:
            total_parts = 0.0
            min_predicates_per_precondition = None
            max_predicates_per_precondition = None

            for action in task.actions:
                num_parts = 0

                if isinstance(action.precondition, conditions.Atom) or isinstance(action.precondition, conditions.NegatedAtom):
                    num_parts = 1
                else:
                    for part in action.precondition.parts:
                        if isinstance(part, conditions.Atom) or isinstance(part, conditions.NegatedAtom):
                            num_parts += 1
                        elif isinstance(part, conditions.Disjunction):
                            num_parts += 1
                        elif isinstance(part, conditions.UniversalCondition):
                            num_parts += 1
                        elif isinstance(part, conditions.ExistentialCondition):
                            num_parts += 1
                        else:
                            print "ERROR: Found a part that wasn't an atom... precondition parsing impossible"
                            print part
                            die

                total_parts += num_parts

                if min_predicates_per_precondition == None or min_predicates_per_precondition > num_parts:
                    min_predicates_per_precondition = num_parts

                if max_predicates_per_precondition == None or max_predicates_per_precondition < num_parts:
                    max_predicates_per_precondition = num_parts

            if num_actions > 0:
                pddl_features['pddlMinPredicatesPerPrecondition'] = min_predicates_per_precondition
                pddl_features['pddlMeanPredicatesPerPrecondition'] = float(total_parts)/float(num_actions)
                pddl_features['pddlMaxPredicatesPerPrecondition'] = max_predicates_per_precondition


        # predicates in effects (min, mean, max)
        # negations in effects (min, mean, max)
        # actions over negative effects (num, ratio)

        num_actions_with_negative_effects = 0.0
        if num_actions > 0:
            total_parts = 0.0
            min_predicates_per_effect = None
            max_predicates_per_effect = None

            total_negations = 0.0
            min_negations_per_effect = None
            max_negations_per_effect = None

            for action in task.actions:
                num_parts = 0
                num_negations = 0

                for effect in action.effects:
                    if isinstance(effect.literal, conditions.Atom):
                        num_parts +=1
                    elif isinstance(effect.literal, conditions.NegatedAtom):
                        num_parts += 1
                        num_negations += 1
                    else:
                        print "Found an effect with a literal that wasn't Atom or NegatedAtom. Need to die."
                        print effect.literal
                        die

                if min_predicates_per_effect == None or min_predicates_per_effect > num_parts:
                    min_predicates_per_effect = num_parts

                if max_predicates_per_effect == None or max_predicates_per_effect < num_parts:
                    max_predicates_per_effect = num_parts

                if min_negations_per_effect == None or min_negations_per_effect > num_negations:
                    min_negations_per_effect = num_negations

                if max_negations_per_effect == None or max_negations_per_effect < num_negations:
                    max_negations_per_effect = num_negations

                if num_negations > 0:
                    num_actions_with_negative_effects += 1

                total_parts += num_parts
                total_negations += num_negations

            if num_actions > 0:
                pddl_features['pddlMinPredicatesPerEffect'] = min_predicates_per_effect
                pddl_features['pddlMeanPredicatesPerEffect'] = float(total_parts)/float(num_actions)
                pddl_features['pddlMaxPredicatesPerEffect'] = max_predicates_per_effect

                pddl_features['pddlMinNegationsPerEffect'] = min_negations_per_effect
                pddl_features['pddlMeanNegationsPerEffect'] = float(total_negations)/float(num_actions)
                pddl_features['pddlMaxNegationsPerEffect'] = max_negations_per_effect


        pddl_features['pddlMarksTotalNumActions'] = num_actions
        if num_actions > 0:
            pddl_features['pddlRatioActionsWithNegativeEffectsOverActions'] = float(num_actions_with_negative_effects)/float(num_actions)

        if isinstance(task.goal, conditions.Conjunction):
            num_goals = len(task.goal.parts)
        elif isinstance(task.goal, conditions.UniversalCondition):
            num_goals = 1
        elif isinstance(task.goal, conditions.Atom):
            num_goals = 1
        elif isinstance(task.goal, conditions.NegatedAtom):
            num_goals = 1
        else:
            print "Goal wasn't a conjunctive condition. Need to die!"
            print task.goal
            die

        pddl_features['pddlNumGoals'] = num_goals
        pddl_features['pddlNumObjects'] = len(task.objects) - len(task.constants)

        num_initial_conditions = 0
        num_equality = 0
        num_function_assignments = 0
        for condition in task.init:
            if isinstance(condition, conditions.Atom):
                if condition.predicate == '=':
                    num_equality += 1
                else:
                    num_initial_conditions += 1
            elif isinstance(condition, conditions.NegatedAtom):
                if condition.predicate == '=':
                    num_equality += 1
                else:
                    num_initial_conditions += 1
            elif isinstance(condition, f_expression.FunctionAssignment):
                num_function_assignments += 1
            else:
                print "Unexpected initial condition that wasn't Atom or NegatedAtom. Need to die!"
                print condition.dump()
                die

        pddl_features['pddlNumInitialConditions'] = num_initial_conditions

        pddl_features['pddlRequiresADL'] = (1.0 if ':adl' in task.requirements.requirements else 0.0)
        pddl_features['pddlRequiresConditionalEffects'] = (1.0 if ':conditional-effects' in task.requirements.requirements else 0.0)
        pddl_features['pddlRequiresDerivedPredicates'] = (1.0 if ':derived-predicates' in task.requirements.requirements else 0.0)
        pddl_features['pddlRequiresDisjunctivePreconditions'] = (1.0 if ':disjunctive-preconditions' in task.requirements.requirements else 0.0)
        pddl_features['pddlRequiresDomainAxioms'] = (1.0 if ':domain-axioms' in task.requirements.requirements else 0.0)
        pddl_features['pddlRequiresEquality'] = (1.0 if ':equality' in task.requirements.requirements else 0.0)
        pddl_features['pddlRequiresExistentialPreconditions'] = (1.0 if ':existential-preconditions' in task.requirements.requirements else 0.0)
        pddl_features['pddlRequiresFluents'] = (1.0 if ':fluents' in task.requirements.requirements else 0.0)
        pddl_features['pddlRequiresQuantifiedPreconditions'] = (1.0 if ':quantified-preconditions' in task.requirements.requirements else 0.0)
        pddl_features['pddlRequiresSafetyConstraints'] = (1.0 if ':safety-constraints' in task.requirements.requirements else 0.0)
        pddl_features['pddlRequiresStrips'] = (1.0 if ':strips' in task.requirements.requirements else 0.0)
        pddl_features['pddlRequiresTyping'] = (1.0 if ':typing' in task.requirements.requirements else 0.0)
        pddl_features['pddlRequiresUniversalPreconditions'] = (1.0 if ':universal-preconditions' in task.requirements.requirements else 0.0)

        if self.simple_pddl_extended_features:
            has_types = 0
            if len(task.types) > 2:
                has_types = 1

            pddl_features['pddlNumConstants'] = len(task.constants)
            pddl_features['pddlNumConstantsAndObjects'] = len(task.objects)

            pddl_features['pddlNumEqualityInitialConditions'] = num_equality
            pddl_features['pddlNumFunctionAssignmentsInInitialConditions'] = num_function_assignments

            pddl_features['pddlHasTypes'] = has_types
            pddl_features['pddlNumTypes'] = len(task.types)-1

            pddl_features['pddlRequiresActionCosts'] = (1.0 if ':action-costs' in task.requirements.requirements else 0.0)
            pddl_features['pddlRequiresNegation'] = (1.0 if ':negation' in task.requirements.requirements else 0.0)
            pddl_features['pddlRequiresNegativePreconditions'] = (1.0 if ':negative-preconditions' in task.requirements.requirements else 0.0)
            pddl_features['pddlRequiresNumericFluents'] = (1.0 if ':numeric-fluents' in task.requirements.requirements else 0.0)
            pddl_features['pddlRequiresObjectFluents'] = (1.0 if ':object-fluents' in task.requirements.requirements else 0.0)
            pddl_features['pddlRequiresDurativeActions'] = (1.0 if ':durative-actions' in task.requirements.requirements else 0.0)
            pddl_features['pddlRequiresDurationInequalities'] = (1.0 if ':duration-inequalities' in task.requirements.requirements else 0.0)
            pddl_features['pddlRequiresContinuousEffects'] = (1.0 if ':continuous-effects' in task.requirements.requirements else 0.0)
            pddl_features['pddlRequiresTimedInitialLiterals'] = (1.0 if ':timed-initial-literals' in task.requirements.requirements else 0.0)
            pddl_features['pddlRequiresPreferences'] = (1.0 if ':preferences' in task.requirements.requirements else 0.0)
            pddl_features['pddlRequiresConstraints'] = (1.0 if ':constraints' in task.requirements.requirements else 0.0)

        return pddl_features
