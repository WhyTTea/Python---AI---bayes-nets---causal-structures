import random #for sampling methods
import pandas as pd #to simplify reading and holding data
from bnetbase import Variable, Factor, BN, restrict_factor, sum_out_variable, normalize

def multiply_factors(Factors):
    '''return a new factor that is the product of the factors in Factors'''
    #first, consider simple case with just two factors to multiply
    if len(Factors) == 0:
        return
    elif len(Factors) == 1:
        new_f = Factors[0]
    elif len(Factors) == 2:
        new_f_scope = []
        f1, f2 = Factors[0], Factors[1]
        
        # capture all variables that are in the scope of both factors
        f1_scope, f2_scope = f1.get_scope(), f2.get_scope()
        
        #copy the factor on the left side of multiplication
        new_f_scope = f1_scope
        for var in f2_scope: #find all factors that are not captured by copying f1_scope
            if var not in new_f_scope:
                new_f_scope.append(var)
        #construct the new factor with the mixed scope of f1 & f2
        new_f = Factor(f1.name+"x"+f2.name, new_f_scope)
        
        # The Factor obj. is initialized, now we need to fill it up with values
        recursive_multiply_factors_helper(f1, f2, new_f_scope, new_f)

    #we are given a list of factors that is longer than two factors
    else:
        while len(Factors) >= 3:
            Factors.append(multiply_factors([Factors.pop(0), Factors.pop(1)]))
            new_f = multiply_factors(Factors)
    #construct a new name for the new factor we are going to build
    return new_f 

def recursive_multiply_factors_helper(f1, f2, vars_scope, new_f):
    
    if len(vars_scope) == 0:
        return new_f.add_value_at_current_assignment(f1.get_value_at_current_assignments() * f2.get_value_at_current_assignments())
    else:
        for val in vars_scope[0].domain():
            vars_scope[0].set_assignment(val)
            recursive_multiply_factors_helper(f1, f2, vars_scope[1:], new_f)
    return
###Orderings
def min_fill_ordering(Factors, QueryVar):
    '''Compute a min fill ordering given a list of factors. Return a list
    of variables from the scopes of the factors in Factors. The QueryVar is
    NOT part of the returned ordering'''
    # find all scopes our factors cover   
    scopes = []
    for f in Factors:
        scopes.append(f.get_scope())
    # compute a list of all variables involved in the span of all of our scopes
    vars = []
    for scope in scopes:
        for element in scope:
            if element not in vars and element != QueryVar:
                vars.append(element)

    scopes_copy = list(scopes)
    vars_copy = list(vars)
    ordered_min_fill = []
    min_fill = [float('inf'),[]]
    # go over Var one-by-one to find all scopes it is involved in   
    while len(vars) != 0:
        master_min_fill = [float('inf'),[],"",[]]
        while len(vars_copy) != 0:
            curr_var = vars_copy.pop(0)
            scopes_to_combine = []
            
            for curr_var_scope in scopes_copy: 
            # finding the scopes with our var
                if curr_var in curr_var_scope:
                    scopes_to_combine.append(curr_var_scope)
            # return the size of the new factor eliminating curr_var & the combined scope
            min_fill = min_fill_combine_sort(scopes_to_combine, curr_var)
            
            # update our absolute minimum before iterating again
            if min_fill[0] < master_min_fill[0]:
                master_min_fill[0] = min_fill[0]
                master_min_fill[1].extend(min_fill[1])
                master_min_fill[2] = curr_var
                master_min_fill[3] = scopes_to_combine
            # scopes_copy.append(min_fill[1])
        
        # update the scopes to remove the scopes we combined into the new_scope
        for item in master_min_fill[3]:
            scopes_copy.remove(item)
        # add the newly built scope 
        scopes_copy.append(master_min_fill[1])
        
        # adding the value to our final answer
        ordered_min_fill.append(master_min_fill[2])
        
        # updating loop variables to move to the next iteration
        vars.remove(master_min_fill[2])
        vars_copy = list(vars)

    return ordered_min_fill

def min_fill_combine_sort(scopes, variable):
    total_min = 0
    combined = []
    # calculate the min size and produce the new scope
    for sublist in scopes:
        if len(sublist) == 1 and sublist[0] != variable:
            combined.append(sublist[0]) 
            total_min += 1
        elif len(sublist) == 1 and sublist[0] == variable:
            continue
        else:
            for element in sublist:
                if element != variable:
                    combined.append(element) 
                    total_min += 1
    
    return [total_min, combined]

def VE(Net, QueryVar, EvidenceVars):
    '''
    Input: Net---a BN object (a Bayes Net)
           QueryVar---a Variable object (the variable whose distribution
                      we want to compute)
           EvidenceVars---a LIST of Variable objects. Each of these
                          variables has had its evidence set to a particular
                          value from its domain using set_evidence.

   VE returns a distribution over the values of QueryVar, i.e., a list
   of numbers one for every value in QueryVar's domain. These numbers
   sum to one, and the i'th number is the probability that QueryVar is
   equal to its i'th value given the setting of the evidence
   variables. For example if QueryVar = A with Dom[A] = ['a', 'b',
   'c'], EvidenceVars = [B, C], and we have previously called
   B.set_evidence(1) and C.set_evidence('c'), then VE would return a
   list of three numbers. E.g. [0.5, 0.24, 0.26]. These numbers would
   mean that Pr(A='a'|B=1, C='c') = 0.5 Pr(A='b'|B=1, C='c') = 0.24
   Pr(A='c'|B=1, C='c') = 0.26

    '''
    distribution = []
    # VE algo step: 1) Define factors
    # extract all factors we need to restrict, multiply and sum out
    factors = Net.factors()

    # VE algo step: 2) Restrict factors
    # go over factors and cross reference it with EvidenceVars to find factos to be restricted
    for i in range(len(factors)):
        for ev_var in EvidenceVars:
            curr_f_scope = factors[i].get_scope()
            if ev_var in curr_f_scope:
                # new_f = restrict_factor(factors[i], var, var.get_evidence())
                # factors[i] = new_f
                factors[i] = restrict_factor(factors[i], ev_var, ev_var.get_evidence())
                
    # VE algo step: 3) Eliminate hidden factors
    # pick the particular order for traversing
    min_fill = min_fill_ordering(factors, QueryVar)

    # find out the factors we need to multiply
    while len(min_fill) != 0:
        var = min_fill[0]
        to_multiply = []
        for factor in factors:
            if var in factor.get_scope():
                to_multiply.append(factor)

        for f in to_multiply:
            factors.remove(f)

        # multiply the factors to generate a new one
        multiplied_f = multiply_factors(to_multiply)

        # sum out the newly generated "multipled" factor
        sum_out_f = sum_out_variable(multiplied_f, var)

        # add the newly summed out factor to the list of factors to keep going over
        factors.append(sum_out_f)

        # move the point in min_fill to the next var
        min_fill.pop(min_fill.index(var))
    
    # VE algo step: 4) Multiply remaining factors (if any)
    distribution = multiply_factors(factors)
    
    # VE algo step: 5) Normalize (if needed)
    # sum_values = 0
    # dist_values = []
    # for value in distribution.get_values():
    #     sum_values += value
    #     dist_values.append(value)
    # print("Disctribution: ",distribution.get_values())
    
    # if sum_values != 1:
    #     dist_values = normalize(dist_values)
    # print("For normalization: ", dist_values)
    # return dist_values
    return normalize(distribution.get_values())

def SampleBN(Net, QueryVar, EvidenceVars):
    '''
     Input: Net---a BN object (a Bayes Net)
            QueryVar---a Variable object (the variable whose distribution
                       we want to compute)
            EvidenceVars---a LIST of Variable objects. Each of these
                           variables has had its evidence set to a particular
                           value from its domain using set_evidence.

    SampleBN returns a distribution over the values of QueryVar, i.e., a list
    of numbers one for every value in QueryVar's domain. These numbers
    sum to one, and the i'th number is the probability that QueryVar is
    equal to its i'th value given the setting of the evidence
    variables.

    SampleBN should generate **1000** samples using the likelihood
    weighting method described in class.  It should then calculate
    a distribution over value assignments to QueryVar based on the
    values of these samples.
    '''
    # Initialize a weight variable to 1 and a sampled data point 1000* times
    # to create a big enough of a sample. 
    master_sample = []
    for i in range(1000):
        # initialize w and sampled datapoint
        w = 1
        datapoint = [None] * len(Net.variables())
        index_QueryVar = Net.variables().index(QueryVar)
        while None in datapoint: # until we assign every value in this particular sample
            discovered = []
            for index_sample_var in range(len(datapoint)): # check if it's EvidenceVar, if so, we know its value

                sample_var = Net.variables()[index_sample_var]
                # need to see if the parent is unassigned. Returnign a factor and parents
                discovered = parse_string_helper(Net, sample_var)
                if check_parents_helper(Net, discovered[1]) == False:
                            continue
                else:
                    if sample_var in EvidenceVars:
                        ev = sample_var.get_evidence()
                        sample_var.set_assignment(ev)
                        w *= discovered[0].get_value_at_current_assignments()
                        datapoint[index_sample_var] = ev
                    else:
                        if discovered[1] == []: # no parents. We caught something line P(C)
                            domain = sample_var.domain() # get the domain to be able to find probabilities
                            # find the weights by picking each probability to make our random selection weighted
                            weights = []
                            for sample_value in domain:
                                sample_var.set_assignment(sample_value)
                                #assembling weight for a proper random dice
                                weights.append(discovered[0].get_value_at_current_assignments())
                            
                            # reset the value assignment after all assignment for weights
                            sample_var.reset_assignment()
                            
                            # pick d with random.choices
                            d = random.choices(domain, weights)

                            # set the assignment so we randomly chose
                            sample_var.set_assignment(d[0])

                            # update datapoint
                            datapoint[index_sample_var] = d

                        else: # they have at least one node in parents list
                            # some of the parents are still unassigned
                            # multiple parents that are assigned
                            for parent in discovered[1]:
                                all_vars = Net.variables()
                                for i_any_var, any_var in enumerate(all_vars):
                                    if any_var.name == parent:
                                        any_var.set_assignment(datapoint[i_any_var])
                            domain = sample_var.domain() # get the domain to be able to find probabilities
                            # find the weights by picking each probability to make our random selection weighted
                            weights = []
                            for sample_value in domain:
                                sample_var.set_assignment(sample_value)
                                weights.append(discovered[0].get_value_at_current_assignments())
                            
                            # reset the value assignment after all assignment for weights
                            sample_var.reset_assignment()
                            
                            # pick d with random.choices
                            d = random.choices(domain, weights)

                            # set the assignment so we randomly chose
                            sample_var.set_assignment(d[0])

                            # update datapoint
                            datapoint[index_sample_var] = d[0]
                            
        master_sample.append([datapoint, w])
    sum_weights = 0
    sum_query_weights = {}
    for iter in QueryVar.domain():
        sum_query_weights[iter] = 0
    ret_sum = []
    for j in master_sample:
        sum_weights += j[1]
        for doma in QueryVar.domain():
            if j[0][index_QueryVar] == doma:
                sum_query_weights[doma] += j[1]
    for key in sum_query_weights.keys():
        ret_sum.append(sum_query_weights.get(key))
    final = [x / sum_weights for x in ret_sum]
        
    return final

def parse_string_helper(Net, Var):
    parents = []
    for factor in Net.factors():
        
        if len(factor.get_scope()) == 1 and (Var in factor.get_scope()):
            return [factor, parents]
        if Var in factor.get_scope():   
            f_name = factor.name
            index_opening_bracket = f_name.index("(")
            index_pipe = f_name.index("|")
            query_var = f_name[index_opening_bracket+1:index_pipe]
            if query_var != Var.name:
                continue
            else: 
                index_closing_bracket = f_name.index(")")
                parents = f_name[index_pipe+1:index_closing_bracket].split(",")
                ret_factor = factor
    return [ret_factor, parents]

def check_parents_helper(Net, parents):
    vars_list = []
    if len(parents) == 0:
        return True
    for parent in parents:
        #print("Parents are:", parents, " and a current parent is: ", parent)
        vars_list.append(Net.get_variable(parent))
        #print("Vars_list: ", vars_list)
    for var in vars_list:
        if var.get_assignment() == None:
            return False
    return True

def CausalModelConfounder():
    """CausalModelConfounder returns a Causal model (i.e. a BN) that
   represents the joint distribution of value assignments to
   variables in COVID-19 data.

   The structure of this model should reflect the assumption
   that age is a COUNFOUNDING variable in the network, and
   is therefore a cause of both Country and Fatality.

    Returns:
        BN: A BN that represents the causal model
    """

    ### READ IN THE DATA
    df = pd.read_csv('data/covid.csv')

    ### DOMAIN INFORMATION
    variable_domains = {
    "Age": ['0-9', '10-19', '20-29', '30-39', '40-49', '50-59', '60-69', '70-79', '80'],
    "Country": ['Italy', 'China'],
    "Fatality": ['YES', 'NO']
    }

    C = Variable("Country", variable_domains.get("Country", None))
    A = Variable("Age", variable_domains.get("Age", None))
    F = Variable("Fatality", variable_domains.get("Fatality", None))

    ### P(A)
    factor_a = Factor("P(Age)", [A])
    values_a = []
    for val in variable_domains["Age"]:
        count_a = (df['Age'] == val).sum()
        total_vals = df.shape[0]
        prob_a = count_a / total_vals
        values_a.append([val, prob_a])
    factor_a.add_values(values_a)
    ###

    ##P(C | A)
    factor_a_c = Factor("P(Country|Age)", [C, A])
    values_a_c = [] 

    for val in variable_domains["Country"]:
        for val2 in variable_domains["Age"]:
            count_a_c = ((df['Country'] == val) & (df['Age'] == val2)).sum()
            prob_a_c = count_a_c / df.shape[0]
            count_a = (df['Age'] == val2).sum()
            prob_a = count_a / df.shape[0]
            values_a_c.append([val, val2, prob_a_c/prob_a])
        factor_a_c.add_values(values_a_c)
    ###

    ### P(F |A, C) = P(F,A,C) / P(A,C)
    factor_fac = Factor("P(Fatality|Age,Country)", [F, A, C])
    values_fac = []
    for val in variable_domains["Fatality"]:
        for val2 in variable_domains["Age"]:
            for val3 in variable_domains["Country"]:
                count_fac = ((df['Fatality'] == val) & (df['Age'] == val2) & (df['Country'] == val3)).sum()
                prob_fac = count_fac / df.shape[0]
                count_ac = ((df['Age'] == val2) & (df['Country'] == val3)).sum()
                prob_ac = count_ac / df.shape[0]
                values_fac.append([val, val2, val3, prob_fac/prob_ac])
            factor_fac.add_values(values_fac)
    ###
    return BN("Confounder Model of BN", [A, C, F], [factor_a, factor_a_c, factor_fac])


def CausalModelMediator():
    """CausalModelConfounder returns a Causal model (i.e. a BN) that
    represents the joint distribution of value assignments to
    variables in COVID-19 data.

    The structure of this model should reflect the assumption
    that age is a MEDIATING variable in the network, and
    is mediates the causal effect of Country on Fatality.

     Returns:
         BN: A BN that represents the causal model
     """

    ### READ IN THE DATA
    df = pd.read_csv('data/covid.csv')

    ### DOMAIN INFORMATION
    variable_domains = {
    "Age": ['0-9', '10-19', '20-29', '30-39', '40-49', '50-59', '60-69', '70-79', '80'],
    "Country": ['Italy', 'China'],
    "Fatality": ['YES', 'NO']
    }

    C = Variable("Country", variable_domains.get("Country", None))
    A = Variable("Age", variable_domains.get("Age", None))
    F = Variable("Fatality", variable_domains.get("Fatality", None))

    ### P(C)
    factor_c = Factor("P(Country)", [C])
    values_c = []
    for val in variable_domains["Country"]:
        count_c = (df['Country'] == val).sum()
        prob_c = count_c / df.shape[0]
        values_c.append([val, prob_c])
    factor_c.add_values(values_c)
    ###

    ### P(A | C) = P(A,C) / P(C)
    ###P(A,C)
    factor_a_c = Factor("P(Age|Country)", [A, C])
    values_a_c = [] 

    for val in variable_domains["Country"]:
        for val2 in variable_domains["Age"]:
            count_ca = ((df['Country'] == val) & (df['Age'] == val2)).sum()
            prob_ca = count_ca / df.shape[0]
            count_c = (df['Country'] == val).sum()
            prob_c = count_c / df.shape[0]
            values_a_c.append([val2, val, prob_ca / prob_c])
        factor_a_c.add_values(values_a_c)
    ###

    ### P(F |A, C) = P(F,A,C) / P(A,C)
    factor_fac = Factor("P(Fatality|Age,Country)", [F, A, C])
    values_fac = []
    for val in variable_domains["Fatality"]:
        for val2 in variable_domains["Age"]:
            for val3 in variable_domains["Country"]:
                count_fac = ((df['Fatality'] == val) & (df['Age'] == val2) & (df['Country'] == val3)).sum()
                prob_fac = count_fac / df.shape[0]
                count_ac = ((df['Age'] == val2) & (df['Country'] == val3)).sum()
                prob_ac = count_ac / df.shape[0]
                values_fac.append([val, val2, val3, prob_fac/prob_ac])
            factor_fac.add_values(values_fac)
    ###

    return BN("CausalModelMediatorBN", [C, A, F], [factor_c, factor_a_c, factor_fac]) 


if __name__ == "__main__":

    model = CausalModelMediator()
    Variables = model.variables()
    Variables[0].set_evidence("Italy")
    probsEstimatedItaly = SampleBN(model, Variables[2], [Variables[0]])
    probsExactItaly = VE(model, Variables[2], [Variables[0]])
    Variables[0].set_evidence("China")
    probsEstimatedChina = SampleBN(model, Variables[2], [Variables[0]])
    probsExactChina = VE(model, Variables[2], [Variables[0]])
    print("Using Mediator Model:")
    print("Exact ACE (P(F=’YES’|Country=’Italy’) - P(F=’YES’|Country=’China’)) = ", probsExactItaly[0] - probsExactChina[0])
    print("Estimated ACE (P(F=’YES’|Country=’Italy’) - P(F=’YES’|Country=’China’)) = ", probsEstimatedItaly[0] - probsEstimatedChina[0])

    model = CausalModelConfounder()
    Factors = model.factors()
    Variables = model.variables()
    ages = ['0-9', '10-19', '20-29', '30-39', '40-49', '50-59', '60-69', '70-79', '80']
    factor_a = Factors[0]
    acc_exact = 0
    acc_estimate = 0
    for index_test, test_value in enumerate(factor_a.get_values()):
        Variables[1].set_evidence("Italy")
        Variables[0].set_evidence(ages[index_test])
        probsEstimatedItaly = SampleBN(model, Variables[2], [Variables[0],Variables[1]])
        probsExactItaly = VE(model, Variables[2], [Variables[0],Variables[1]])
        Variables[1].set_evidence("China")
        Variables[0].set_evidence(ages[index_test])
        probsEstimatedChina = SampleBN(model, Variables[2], [Variables[0],Variables[1]])
        probsExactChina = VE(model, Variables[2], [Variables[0],Variables[1]])
        acc_exact += test_value*(probsExactItaly[0] - probsExactChina[0])
        acc_estimate += test_value*(probsEstimatedItaly[0] - probsEstimatedChina[0])
    print("Using Confounder Model:")
    print("Exact ACE Sum_over_Ages (P(Age)*(P(F=’YES’|Country=’Italy’,Age) - P(F=’YES’|Country=’China’,Age))) = ", acc_exact)
    print("Estimated ACE Sum_over_Ages (P(Age)*(P(F=’YES’|Country=’Italy’,Age}) - P(F=’YES’|Country=’China’,Age}))) = ", acc_estimate)



