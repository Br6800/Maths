import pandas as pd
import random as r
from scipy.special import stirling2 as s
from math import comb as c
num_trials = 330
#your_number = sum([j / 1625**330 [(-1)**i *c(6,i)*(1625-i)**330 for i in [0,3,4,5,6]])
#print("{:.50f}".format(your_number))
"""
success=  0
for i in range(10000):
    d = pd.DataFrame()
    d['rolls'] = [r.randint(1,1625) for j in range(330)]
    success += len(set(d[d['rolls'] <= 6]['rolls'])) >= 4
    #print(set(d[d['rolls'] <= 4]))
print(success / 10000)
#print(d)
print(c(6,3)*(1622/1625)**num_trials)
"""
seqs = [[i,j,k,l]
    for i in range(1,6) for j in range(1,6) for k in range(1,6) for l in range(1,6)]
print(sum([len(set(i).intersection({1,2,3})) >= 2 for i in seqs]))


def inner(q_,m_,No_,n_):
    return sum([(-1) ** j * c(q_-m_,j)*((No_-m_-j)/No_)**n_ for j in range(q_-m_+1)])
def inner2(q_,m_,No_,n_):
    return sum([(-1) ** j * c(m_,j)*((No_-q_+m_-j)/No_)**n_ for j in range(m_+1)])
num_trials = 330
q = 6
k = 4
No = 1625
total = sum([c(q,m)*inner(q,m,No,num_trials) for m in range(q-k+1)])
total2 = sum([c(q,q-m)*inner2(q,m,No,num_trials) for m in range(k,q+1)])
print(total2)
print(total)
