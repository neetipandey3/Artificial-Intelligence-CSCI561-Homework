import copy

dict_of_states = {}
repetition = {}
queries_repetition = []

def main():
    global current_query
    text_file = open("input.txt", "r")
    output_file = open('output.txt', 'w')
    queries = read_queries(text_file)
    kb = read_kb(text_file)
    working_kb = copy.deepcopy(kb)
    result = []
    for q in queries:
        q = q.replace(" ", "")
        current_query = negation_of(q)
        repetition = {}
        queries_repetition = []
        dict_of_states = {}
        if FOL_resolution(current_query, copy.deepcopy(kb)):
            #print(q + "TRUE")
            s = "TRUE"
        else:
            #print(q + "FALSE")
            s = "FALSE"
        result.append(s)
    print(*result, sep = "\n")
    for i in result:
        output_file.write(i+"\n")



FAILURE = "failure"
dict_clauses= {}
resolved = []
list_of_attribs = []

not_to_match = {}
last_queries = []
branches = {}
list_count = []
list_found = {}



def FOL_resolution(query, KB):
    query_matched = {}
    matching_list = []
    query_to_resolve = []
    resolvent = ''
    if query == '':
        return False
    queries_repetition.append(query)

    repetition = {x: queries_repetition.count(x) for x in queries_repetition}
    for k, v in repetition.items():
        if k == query and repetition[k] > 10:
            return False



    sub_queries = query.split("|")

    for sub_query in sub_queries:
        if sub_query not in list_found:
            matching_list = find_matching_predicate(sub_query, KB)
            if matching_list:
                query_to_resolve.append(sub_query)
                query_to_resolve.append(query)
                break

    if not matching_list:
        if resolvent:
            for each in resolvent:
                if each in KB:
                    KB.remove(each)
        if FOL_resolution(current_query, KB):
            return True
        else:
            return False



    for matching_clause in matching_list:
        if dict_of_states and query_to_resolve[1] in dict_of_states.keys() and matching_clause[1] in dict_of_states[query_to_resolve[1]][1]:
            if not (len(dict_of_states[query_to_resolve[1]][1]) == 1 and len(matching_list) == 1) and not ((dict_of_states[query_to_resolve[1]][0]) == matching_clause[0]):
                continue

        resolvent, theta = FOL_resolve(query_to_resolve, matching_clause)
        if resolvent == '' and FAILURE not in theta:
            return True
        elif resolvent != '' and not KB:
            return False
        elif FAILURE in theta:
            last_query = last_queries.pop()
            if dict_of_states and query_to_resolve[1] in dict_of_states:
                list_of_not = dict_of_states[query_to_resolve[1]][1]
                if matching_clause[1] not in list_of_not:
                    list_of_not.append(matching_clause[1])
                dict_of_states[query_to_resolve[1]][1] = list_of_not
            else:
                dict_of_states[query_to_resolve[1]] = [negation_of(query_to_resolve[0]), [matching_clause[1]], ['']]

            if last_query in list_count:
                last_query = last_queries.pop()
            last_state = dict_of_states[last_query]
            if last_state[2]:
                resolved_to_remove = last_state[2].pop()

            if resolved_to_remove in KB:
                KB.remove(resolved_to_remove)

            for key, val in dict_of_states.items():
                if resolved_to_remove in dict_of_states[key][1]:
                    dict_of_states[key][1].remove(resolved_to_remove)
                if resolved_to_remove in dict_of_states[key][2]:
                    dict_of_states[key][2].remove(resolved_to_remove)
            if last_query not in list_count:
                list_count.append(last_query)
            if last_query == '':
                last_query = current_query
            if FOL_resolution(last_query, KB):
                return True
            else:
                return False
        else:
            break

    if resolvent not in KB:
        last_queries.append(query_to_resolve[1])
        KB.append(resolvent)
        resolved.append(resolvent)
        queries = []
        list_of_matching_clauses = []
        list_of_resolvents = []
        if query_to_resolve[1] not in dict_of_states:
            list_of_matching_clauses.append(matching_clause[1])
            list_of_resolvents.append(resolvent)# 4
        else:
            list_of_matching_clauses = dict_of_states[query_to_resolve[1]][1]
            if matching_clause[1] not in list_of_matching_clauses:
                list_of_matching_clauses.append(matching_clause[1])
            list_of_resolvents = dict_of_states[query_to_resolve[1]][2]
            list_of_resolvents.append(resolvent)
        queries.append(negation_of(query_to_resolve[0]))  # 2
        queries.append(list_of_matching_clauses)  # 3
        queries.append(list_of_resolvents)
        if resolvent != '':
            dict_of_states[query_to_resolve[1]] = queries
    return FOL_resolution(resolvent, KB)


def FOL_resolve(query, matching_clause):
    theta = {}
    literals = []
    clause_1 = []
    clause_2 = []

    if not query[1] and not matching_clause[1]:
        return '', []

    unify(negation_of(query[0]), matching_clause[0], theta)
    if FAILURE in theta:
        return '', theta

    if query[1]:
        clause_1 = query[1].split("|")
        clause_1.remove(query[0])
    if matching_clause[1]:
        clause_2 = matching_clause[1].split("|")
        clause_2.remove(matching_clause[0])
    for literal in clause_1:
        literals.append(substitute(literal, theta))
    for literal in clause_2:
        substituted = substitute(literal, theta)
        if substituted not in literals:
            literals.append(substituted)
    #resolvent = "|".join(literals)

    predicate_each = []
    theta = {}
    same_literals = {}
    found_factoring_lit = {}
    pairs_of_unification = {}
    flag = False
    factored_literals = []
    for i in range(len(literals)):
        for j in range(len(literals)):
            if literals[i] != literals[j] and get_predicate(literals[i]) == get_predicate(literals[j]) and len(get_args(literals[i]).split(",")) == len(get_args(literals[j]).split(",")):
                unify(literals[i], literals[j], theta)
                if theta and not FAILURE in theta:
                    break;

    if theta:
        for each_literal in literals:
            subs = substitute(each_literal, theta)
            if subs not in factored_literals:
               factored_literals.append(subs)

    if theta:
        resolvent = "|".join(factored_literals)
    else:
        resolvent = "|".join(literals)





    return resolvent, theta


def find_matching_predicate(query, KB):
    matched_list = []

    to_search = negation_of(query)

    for sentence in KB:
        literals = sentence.split("|")
        for literal in literals:
            matched_clause = []
            if to_search == literal or ((get_predicate(literal) == get_predicate(to_search)) and (len(get_args(to_search).split(",")) == len(get_args(literal).split(",")))):
                matched_clause.append(literal)
                matched_clause.append(sentence)

                matched_list.append(matched_clause)

    return matched_list


def unify(x, y, theta):
    if theta:
        if FAILURE in theta:
            return theta
    if x == y:
        return theta
    if is_variable(x):
        unify_var(x, y, theta)
    elif is_variable(y):
        unify_var(y, x, theta)
    elif is_compound(x) and is_compound(y):
        unify(get_predicate(x), get_predicate(y), theta)
        return unify(get_args(x), get_args(y), theta)
    elif is_list(x) and is_list(y):
        first_a, rest_a = split_list(x)
        first_b, rest_b = split_list(y)
        unify(first_a, first_b, theta)
        return unify(rest_a, rest_b, theta)
    else:
        theta[FAILURE] = FAILURE
        return theta


def unify_var(var, x, theta):
    if var in theta.keys():
        return unify(theta[var], x, theta)
    elif occur_check(var, x, theta):
        theta[FAILURE] = FAILURE
    else:
        x = substitute(x, theta)
        theta[var] =  x


def occur_check(var, x, s):
    if var == x:
        return True
    elif is_variable(x) and x in s:
        return occur_check(var, s[x], s)
    elif is_compound(x):
        return (occur_check(var, get_predicate(x), s) or
                occur_check(var, get_args(x), s))
    else:
        return False


def is_compound(x):
    if "(" in x:
        return True
    else:
        return False


def get_args(a):
    if is_compound(a):
        return a[a.find("(")+1:len(a)-1]


def get_predicate(a):
    return a[0:a.find("(")]


def is_list(x):
    if "," in x:
        return True


def split_list(x):
    if "(" in x[0:x.find(",")]:
        return x[0:x.find(")")+1], x[x.find(")")+2:len(x)]
    else:
        return x[0:x.find(",")], x[x.find(",")+1:len(x)]


def is_variable(x):
    if len(x) == 1 and x.islower() and not is_list(x) and not is_compound(x):
        return True
    elif x[0].islower() and not is_list(x) and not is_compound(x):
        return True
    else:
        return False


def negation_of(literal):
    if literal[0] == "~":
        return literal[1:]
    else:
        return "~" + literal


def is_fact(goal):
    for i in get_args(goal).split(","):
        if is_variable(i):
            return False
    return True


def get_variable(str_args):
    args = str_args.split(",")
    for arg in args:
        if not is_variable(arg):
            args.remove(arg)
    return args


def substitute(statement, subst):
    if is_compound(statement):
        for i in get_variable(get_args(statement)):
            if i in subst.keys():
                statement = replace_var_val(statement, i, subst[i])
    return statement


def replace_var_val(x, var, val):
    if is_compound(x):
        u_arg = []
        for arg in get_args(x).split(","):
            if is_variable(arg) and arg == var:
                u_arg.append(val)
            elif is_compound(arg):
                u_arg.append(replace_var_val(arg, var, val))
            else:
                u_arg.append(arg)
        x = get_predicate(x)+"("+",".join(u_arg)+")"
    return x


# Reading the input file
def read_queries(text_file):
    queries = []
    for i in range(int(text_file.readline())):
        queries.append(text_file.readline().strip())
    return queries


def read_kb(text_file):
    kb = []
    for i in range(int(text_file.readline())):
        st = text_file.readline().strip()
        st = st.replace(" ", "")
        clause = standardize(st, i)
        kb.append(clause)
    return kb


def standardize(clause, i):
    l = []
    literals = clause.split("|")
    for literal in literals:
        args = get_args(literal).split(",")
        arg = []
        for v in args:
            if is_variable(v):
                arg.append(v + str(i))
            else:
                arg.append(v)
        l.append(get_predicate(literal) + "("+",".join(arg)+")")
    std_clause = "|".join(l)
    return std_clause


main()
