import random
import numpy as np
import matplotlib.pyplot as plt
from scipy import special as sp
sims = 0
object_types_no = 5
objects_amount = 50
draws_bucket = [[] for i in range(object_types_no)]
p1 = 0
p2 = 0
dumb_var1 = 0
dumb_var2 = 0
def flatten(xss):
    return [x for xs in xss for x in xs]
while sims < 70000:
    sims += 1

    lst = [random.randrange(object_types_no) for i in range(objects_amount)]

    """
    lst = [0 for i in range(17)] + [1 for i in range(17)] + \
        [2 for i in range(17)] + [3 for i in range(17)] + \
        [4 for i in range(16)] + [5 for i in range(16)]
    """
      # ========================== MODIFIED SECTION ==========================
    # Zipfian distribution (skewed towards smaller numbers)
    # Create Zipfian probabilities: P(i) = 1 / i, normalized to sum to 1
    weights = np.array([1 / (i + 1) for i in range(object_types_no)])

    #weights = [0.33, 0.25, 0.15, 0.09,0.09,0.09]
    #weights = [100 / object_types_no for i in range(object_types_no)]
    weights = np.array(weights)
    weights /= weights.sum()  # Normalize so they sum to 1
    #print(weights)
# Sample exactly 100 elements based on these probabilities
    lst = np.random.choice(object_types_no, size=objects_amount, p=weights).tolist()
    lst = flatten([[i] * int(objects_amount / object_types_no) for i in range(object_types_no)])
    p2 += 1
    if len(set(lst)) == object_types_no:
        p1 += 1
    #plt.hist(lst)
    #plt.show()
#    print(f'list len: {len(lst)}')
#    print('list', lst)
    # Pareto distribution (skewed towards smaller numbers)
#    lst = (np.random.pareto(a=3, size=objects_amount) * object_types_no / 2).astype(int)
#    lst = [x if x < object_types_no else object_types_no - 1 for x in lst]  # Clamp values to [0, object_types_no-1]
    # ======================================================================
    for i in range(object_types_no):
        lst_temp = lst.copy()
        seeds = set()
        draws = 0
        if set(lst_temp).issubset(seeds):
            draws_bucket[i].append(objects_amount)  # Or use np.nan to indicate missing values
        else:
            while len(seeds) < i + 1 and lst_temp:
                draws += 1
                seed = lst_temp.pop(random.randrange(len(lst_temp)))
                seeds.add(seed)
                if draws == 14 and i == 4:
                    dumb_var2 += 1
                    if len(seeds) == 3:
                        dumb_var1 += 1
            draws_bucket[i].append(draws)




print([(np.mean(i),np.std(i)) for i in draws_bucket])
print()
print()
print(f'Proportion of sims where all seed types were in packet: {p1 / p2}')
print(f'dumb proportion: {dumb_var1 / dumb_var2}')
#print(factor)
#print()
#print(total)
import matplotlib.pyplot as plt
import scipy.stats as stats
# Sample data
for i in range(len(draws_bucket)):
    data = draws_bucket[i]
    data.sort()


    # Find the 95th percentile index
    threshold = np.percentile(data, 95, interpolation='higher')
    print('thresh:', threshold)
    print([sp.comb(object_types_no,j)*sp.factorial(j)*sp.stirling2(threshold,j) / (object_types_no ** threshold) for j in range(object_types_no)])
    # Plot histogram
    mean = np.mean(data)
    std_dev = np.std(data)

    # Generate normally distributed data with same mean and std dev
    normal_data = np.random.normal(mean, std_dev, size=70000)
    # Create figure and axis
    # Define common bin edges (integer values from min to max of data)
    bin_edges = np.arange(min(data) - 5, max(data) + 5 + 1, 1)  # +1 to include max+5

    # Compute percentiles for different cutoffs
    lower_95 = mean - 1.96 * std_dev  # 2.5% cutoff (two-tailed)
    upper_95 = mean + 1.96 * std_dev  # 97.5% cutoff (two-tailed)
    one_tail_5 = mean + 1.645 * std_dev  # 5% one-tailed (right-side only)

    # Create figure and axis
    plt.figure(figsize=(10, 6))

    # Plot histogram of original discrete data (filled bars)
    plt.hist(data, bins=bin_edges, align='mid', color='lightblue', edgecolor='black', alpha=0.7, label="Original Data", density=True)

    # Plot histogram of normal distribution (outlined, no fill)
    plt.hist(normal_data, bins=bin_edges, histtype='step', color='red', linewidth=2, density=True, label="Normal Approximation")

    # Add vertical lines for the cutoffs
    plt.axvline(lower_95, color='green', linestyle='dashed', linewidth=2, label="Normal 2.5th Percentile (Lower Tail)")
    plt.axvline(upper_95, color='blue', linestyle='dashed', linewidth=2, label="Normal 97.5th Percentile (Upper Tail)")
    plt.axvline(one_tail_5, color='red', linestyle='dashed', linewidth=2, label="Normal 5% One-Tailed Cutoff (Right)")
    plt.axvline(threshold, color='green', linestyle='solid', linewidth=2, label=f"Actual 5% One-Tail. This is discrete, {threshold}.")

    # Adjust x-axis limits
    plt.xlim(max(min(data) - 5,0), max(data) + 5)

    # Labels and legend
    plt.xlabel("Value")
    plt.ylabel("Density")
    plt.title("Histogram of Discrete Data and Normal Approximation")
    plt.xticks(range(max(min(data) - 5,0), max(data) + 5, 5))  # Adjust x-axis ticks
    plt.legend()

    # Show plot
    plt.show()
#print(lst)
#print(f'list len: {len(lst)}')
