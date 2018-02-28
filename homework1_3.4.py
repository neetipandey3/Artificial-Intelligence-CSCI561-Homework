import time
import random
import math

start_time = time.time()
input_file = open("./input.txt", "r", encoding="utf-8")
output_file = open("./output.txt", "w", encoding="utf-8")
method_to_use = input_file.readline().strip()
size_of_nursery = int(input_file.readline())
no_of_lizards = int(input_file.readline())
input_matrix = []

for _ in range(size_of_nursery):
    input_matrix.append(list(input_file.readline().strip()))
    if(len(input_matrix[-1]) != size_of_nursery):
        output_file.write("FAIL")
        output_file.close()
        exit("FAIL")

solution = input_matrix
lizards = 0
lizard_locations = []
lizards_0 = []
lizards_2 = []
conflicting_positions = {(-1, -1):(-1, -1)}

#Get all the non-tree postions in a list
for col in range(size_of_nursery):
    for row in range(size_of_nursery):
        if(input_matrix[row][col] == '0'):
            lizards_0.append((row, col))
        if(input_matrix[row][col] == '2'):
            lizards_2.append((row, col))

if(len(lizards_0) < no_of_lizards):
    output_file.write("FAIL")
    output_file.close()
    exit("FAIL")

if(lizards_2 == [] and no_of_lizards > size_of_nursery):
    output_file.write("FAIL")
    output_file.close()
    exit("FAIL")

#Function to place lizard recursively on the grid
def place_lizard_dfs(solution, lizards, conflicting_positions) :
    if(time.time() - start_time > 285):
        return False

    if(lizards == no_of_lizards):
        return True

    for (row, col) in lizards_0:
        if(is_lizard_safe_dfs(solution, row, col, lizard_locations, conflicting_positions)):
            solution[row][col] = 1
            lizard_locations.append((row, col))

            if(place_lizard_dfs(solution, lizards+1, conflicting_positions)):
                return True

            solution[row][col] = 0
            lizard_locations.pop()

    return False

def find_bfs_solution(no_of_lizards, conflicting_positions):
    if(no_of_lizards==0):
        return [[]]
    else:
        return place_lizard_bfs(find_bfs_solution(no_of_lizards-1, conflicting_positions), no_of_lizards-1)

def place_lizard_bfs(existing_solution, next_move):
    if(time.time() - start_time > 285):
        return [[]]
    list_of_solution = []
    for each_existing_path in existing_solution:
        for row, col in lizards_0:
            if(is_lizard_safe_bfs(each_existing_path, row, col, conflicting_positions)):
                list_of_solution.append(each_existing_path + [(row, col)])
                if(len(each_existing_path) == no_of_lizards):
                    return list_of_solution
    return list_of_solution

#DFS::Function to check if the lizard is safe at the chosen row, col poistion
def is_lizard_safe_dfs(solution, new_row, new_col, lizard_locations, conflicting_positions):
    for row, col in lizard_locations:
        if ((new_row, new_col) in conflicting_positions[(row, col)] or (row == new_row and col == new_col)):
            return False
    return True

#BFS:: Function to check if the lizard is safe at the chosen row, col poistion
def is_lizard_safe_bfs(each_existing_path, new_row, new_col, conflicting_positions):
    for row, col in each_existing_path:
        if ((new_row, new_col) in conflicting_positions[(row, col)] or (row == new_row and col == new_col)):
            return False
    return True

#Simulated Annealing method
def find_SA_solution():
    T = 1000
    delta_E = 0
    iteration = 0

    current_state = get_initial_state()
    if(get_num_conflicts(current_state) == 0):
        return current_state

    while(True):
        if((time.time()-start_time) > 285):
            return []
        T = schedule(T, iteration)
        if T == 0:
            return []
        next_state = get_next_state(current_state)
        next_state_conflicts = get_num_conflicts(next_state)
        if(next_state_conflicts == 0):
            return next_state
        cur_state_conflicts =  get_num_conflicts(current_state)
        delta_E =  next_state_conflicts - cur_state_conflicts
        P = math.exp(delta_E/T)
        if((time.time()-start_time) > 185):
            solve(solution, lizards, get_conflicting_positions())
            exit()
        random_probability = random.uniform(0.0, 1.0)
        if(delta_E > 0):
            current_state = next_state
        elif(random_probability <= P):
            current_state = next_state
        iteration+=1

    return current_state

#Temperature schedule must decrease
#Need to ensure using a logarithmic division function, as we don't want T to be 0; just closer to 0
def schedule(temperature, iteration):
    #return temperature/math.log(size_of_nursery + iteration)
    return temperature * 0.99999

#Get the initial state of lizard positions - Random
def get_initial_state():
    state = []
    liz = 0
    while( liz < no_of_lizards):
        liz_row = random.randint(0, size_of_nursery-1)
        liz_col = random.randint(0, size_of_nursery-1)
        if((liz_row, liz_col) not in state and solution[liz_row][liz_col] != '2'):
            state.append((liz_row, liz_col))
            liz+=1

    return state

#Genereate the neighbour state of lizard positions - Random??
#Move the queens
def get_next_state(current_state):
    state = []
    liz = 0

    pick_lizard = random.randint(0, size_of_nursery-1)
    while( liz < no_of_lizards):
        liz_row = random.randint(0, size_of_nursery-1)
        liz_col = random.randint(0, size_of_nursery-1)
        if((liz_row, liz_col) not in state and solution[liz_row][liz_col] != '2'):
            state.append((liz_row, liz_col))
            liz+=1

    return state

def get_num_conflicts(state):
    temp_conflicting_pos = {(-1, -1):(-1, -1)}
    conflicting_positions = get_conflicting_positions();
    no_of_conflicts = 0

    for row, col in state:
        temp_conflicting_pos.update({(row, col): conflicting_positions[(row, col)]})

    for (row, col), pos_list in temp_conflicting_pos.items():
        for (s_row, s_col) in state:
            if ((s_row, s_col) in pos_list):
                no_of_conflicts+=1

    return no_of_conflicts


#Function to get the master dictionary for all the conflicting positions with each position as the key
def get_conflicting_positions():
    for row, col in lizards_0:
        temp_list = []
        #Check downward
        rows = row+1
        while(rows <= size_of_nursery-1):
            if(solution[rows][col] == '2'):
                break
            temp_list.append((rows, col))
            rows+=1

        #Check upward
        rows = row-1
        while(rows >= 0):
            if(solution[rows][col] == '2'):
                break
            temp_list.append((rows, col))
            rows-=1

        #Check forward
        cols = col+1
        while(cols <= size_of_nursery-1):
            if(solution[row][cols] == '2'):
                break
            temp_list.append((row, cols))
            cols+=1

        #Check backward
        cols = col-1
        while(cols >= 0):
            if(solution[row][cols] == '2'):
                break
            temp_list.append((row, cols))
            cols-=1

        #Check forward down diagonal
        rows = row+1
        cols = col+1
        while(rows <= size_of_nursery-1 and cols <= size_of_nursery-1):
            if(solution[rows][cols] == '2'):
                break
            temp_list.append((rows, cols))
            rows+=1
            cols+=1

        #Check backward up diagonal
        rows = row-1
        cols = col-1
        while(rows >=0 and cols >=0):
            if(solution[rows][cols] == '2'):
                break
            temp_list.append((rows, cols))
            rows-=1
            cols-=1

        #Check forward up diagonal
        rows = row-1
        cols = col+1
        while(rows >= 0 and cols <= size_of_nursery-1):
            if(solution[rows][cols] == '2'):
                break
            temp_list.append((rows, cols))
            rows-=1
            cols+=1

        #Check backward down diagonal
        rows = row+1
        cols = col-1
        while(rows <= size_of_nursery-1 and cols >= 0):
            if(solution[rows][cols] == '2'):
                break
            temp_list.append((rows, cols))
            rows+=1
            cols-=1

        conflicting_positions.update({(row, col): temp_list})
    return conflicting_positions

#Get the master dictionary for all the conflicting positions for each possible position on the grid
conflicting_positions = get_conflicting_positions()

def solve(solution, lizards, conflicting_positions):
    if(place_lizard_dfs(solution, lizards, conflicting_positions)):
        print("OK")
        output_file.write("OK\n")
        for i in range (size_of_nursery):
            print(*solution[i], sep = "")
            output_file.write(''.join(map(str, solution[i])))
            output_file.write('\n')
    else:
        print("FAIL")
        output_file.write("FAIL")

def solve_using_bfs(conflicting_positions):
    print_solution = find_bfs_solution(no_of_lizards, conflicting_positions)
    if(len(print_solution) > 0):
        output_file.write("OK\n")
        print("OK")
        for row, col in print_solution[0]:
            solution[row][col] = 1
        for i in range (size_of_nursery):
            print(*solution[i], sep = "")
            output_file.write(''.join(map(str, solution[i])))
            output_file.write('\n')
    else:
        print("FAIL")
        output_file.write("FAIL")

def solve_using_SA():
    print_solution = find_SA_solution()
    if(print_solution):
        output_file.write("OK\n")
        print("OK")
        for (row, col) in print_solution:
            solution[row][col] = 1
        for i in range (size_of_nursery):
            print(*solution[i], sep = "")
            output_file.write(''.join(map(str, solution[i])))
            output_file.write('\n')
    else:
        print("FAIL")
        output_file.write("FAIL")


if(method_to_use == 'DFS'):
    solve(solution, lizards, conflicting_positions)
elif(method_to_use == 'BFS'):
    solve_using_bfs(conflicting_positions)
elif(method_to_use == 'SA'):
    solve_using_SA()
else:
    exit("FAIL")
    output_file.write("FAIL")
output_file.close()

#print("Total duration = {}".format(time.time()-start_time))
