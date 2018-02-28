import time
import copy

start_time = time.time()
input_file = open("./input.txt", "r", encoding="utf-8")
output_file = open("./output.txt", "w", encoding="utf-8")
board_size = int(input_file.readline())
no_fruits_types = input_file.readline()
time_left = input_file.readline()

input_matrix = []

for _ in range(board_size):
    input_matrix.append(list(input_file.readline().strip()))
    if(len(input_matrix[-1]) != board_size):
        output_file.write("FAIL")
        output_file.close()
        exit("FAIL")

board = copy.deepcopy(input_matrix)
state = []
column_index = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'U', 'Z']

star_starts_at_dict = {}
neighbours_dict = {}
def find_next_neighbours(state):
    #print("find_next_neighbours")
    #print("STATE..{}".format(state))
    for col in range(board_size):
        for row in range(board_size-1, -1, -1):
            selected_fruit = state[row][col]
            if selected_fruit == '*':
                star_starts_at_dict.update({col : row})
                break;
            neighbours = []
            if (row-1 >= 0 and state[row-1][col] == selected_fruit):
                neighbours.append((row-1, col))
            if (col-1 >= 0 and state[row][col-1] == selected_fruit):
                neighbours.append((row, col-1))
            if (row+1 < board_size and state[row+1][col] == selected_fruit):
                neighbours.append((row+1, col))
            if (col+1 < board_size and state[row][col+1] == selected_fruit):
                neighbours.append((row, col+1))
            neighbours_dict.update({(row, col): neighbours})
            #print("star_starts_at_dict {}".format(star_starts_at_dict))
    return neighbours_dict

def find_cluster(row, col):
    """find the cluster of same fruit type based on the selected position"""
    cluster = []
    tracker = []
    cluster.append((row, col))
    tracker.append((row, col))
    while(tracker):
        neighbours = neighbours_dict[tracker.pop()]
        for (r, c) in neighbours:
            if ((r, c) not in cluster):
                cluster.append((r, c))
                tracker.append((r, c))
                #print("cluster {}".format(cluster))
    return cluster


def get_next_state(cur_board, row, col):
    """ get the next board state by finding and then sliding the cluster
    Returns:
    Next board state"""

    cur_board
    row_cut_off_dict = {}
    selected_cluster = find_cluster(row, col)
    for (r, c) in selected_cluster:
        #print("r {} c {}".format(r, c))
        cur_board[r][c] = '*'
        if(row_cut_off_dict.get(c)):
            row_cut_off_dict[c] = max(row_cut_off_dict[c], r)
        else:
            row_cut_off_dict.update({c : r})

    for column, lowest_row_to_slide_to in row_cut_off_dict.items():
        counter = 0
        for row in range(lowest_row_to_slide_to, -1, -1):
            if(cur_board[row][column] == '*'):
                counter += 1
            else:
                if(row+counter < board_size):
                    temp = cur_board[row+counter][column]
                    cur_board[row+counter][column] = cur_board[row][column]
                    cur_board[row][column] = temp

    return cur_board



def find_next_moves():
    """Find next set of available moves - excluding the stars on board
    Returns:
    1. Dictionary of best set of moves - KEY = MOVE; VALUE = CLUSTER_SIZE
    """
    next_moves = []
    best_set_of_moves = {}
    columns_with_stars = star_starts_at_dict.keys()
    for col in range(board_size):
        for row in range(board_size-1, -1, -1):
            if(col in columns_with_stars and row == star_starts_at_dict.get(col)):
                break
            next_moves.append((row, col))

    while(next_moves):
        row, col = next_moves.pop()
        cluster = find_cluster(row, col)
        best_set_of_moves.update({(row, col): len(cluster)})
        next_moves = set(next_moves) - set(cluster)


    return best_set_of_moves


best_score = 0
child_score = 0
moves = []
boards = []

def alpha_beta_minmax(net_score, depth, alpha=float("-inf"), beta=float("inf"), MAX = True):
    """Find the best move using minimax-alpha-beta-pruning
    Returns:
    1. best score
    2. best move """
        #if time_left() < TIMER_THRESHOLD:
        #    raise Timeout()

    find_next_neighbours(boards[-1])


    next_moves = find_next_moves()

    if (not next_moves):
        #print("No moves")
        return net_score, (-1, -1)

    #best_score = float("-inf") if MAX else float("inf")
    selected_row, selected_col = list(next_moves.keys())[0]

    best_score = alpha if MAX else beta

    if MAX:
        for (move_row, move_col), value in next_moves.copy().items():
            (move_row, move_col) = [key for key, value in next_moves.items() if value == max(next_moves.values())][0]
            boards.append(get_next_state(boards[-1], move_row, move_col))
            child_score = net_score + get_score(next_moves.get(move_row, move_col))
            alpha_beta_minmax(net_score, depth-1, alpha, beta, not MAX)
            boards.pop()

            if child_score >= best_score:
                best_score, (selected_row, selected_col) = child_score, (move_row, move_col)
            if best_score >= beta:
                return best_score, selected_row, selected_col
            #If branch utility is greater than current score of alpha for MAX nodes, update alpha """
            alpha = max(alpha, best_score)


    else:
        for (move_row, move_col), value in next_moves.copy().items():
            boards.append(get_next_state(boards[-1], move_row, move_col))
            child_score = net_score - get_score(next_moves.get(move_row, move_col))
            alpha_beta_minmax(child_score, depth-1, alpha, beta, MAX)
            boards.pop()

            if child_score <= best_score:
                best_score, (selected_row, selected_col) = child_score, (move_row, move_col)

            if best_score <= alpha:
                return best_score, selected_row, selected_col

            beta = min(beta, best_score)


    if(depth == 0):

        return best_score, (selected_row, selected_col)

    return best_score, selected_row, selected_col

def get_score(node_value):
    return node_value**2


boards = []
boards.append(copy.deepcopy(input_matrix))

x, row, col = alpha_beta_minmax(0, depth = 2, alpha=float("-inf"), beta=float("inf"), MAX=True)

output_file.write(column_index[col]+str(row+1))
output_file.write('\n')


for i in range (board_size):
    print(*board[i], sep = "")

star_starts_at_dict = {}

find_next_neighbours(board)
result = get_next_state(board, row, col)

print("\nOutput________\n")
print("{}".format(column_index[col]+str(row+1)))
for i in range (board_size):
    print(*result[i], sep = "")
    output_file.write(''.join(map(str, result[i])))
    output_file.write('\n')

output_file.close()
#print(time.time() - start_time)
