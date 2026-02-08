import numpy as np
import util

from linear_model import LinearModel


def main(train_path, eval_path, pred_path):
    """Problem 1(b): Logistic regression with Newton's Method.

    Args:
        train_path: Path to CSV file containing dataset for training.
        eval_path: Path to CSV file containing dataset for evaluation.
        pred_path: Path to save predictions.
    """
    x_train, y_train = util.load_dataset(train_path, add_intercept=True)
    # *** START CODE HERE ***
    x_eval, y_eval = util.load_dataset(eval_path, add_intercept=True)
    model = LogisticRegression(eps=1e-5)
    model.fit(x_train,y_train)
    y_pred = model.predict(x_eval)
    util.plot(x_train, y_train, model.theta, 'output/p01b_2total.png')
    np.savetxt(pred_path, y_pred > 0.5, fmt='%d')

    # *** END CODE HERE ***


class LogisticRegression(LinearModel):
    """Logistic regression with Newton's Method as the solver.

    Example usage:
        > clf = LogisticRegression()
        > clf.fit(x_train, y_train)
        > clf.predict(x_eval)
    """
    def fit(self, x, y):
        """Run Newton's Method to minimize J(theta) for logistic regression.

        Args:
            x: Training example inputs. Shape (m, n).
            y: Training example labels. Shape (m,).
        """
        # *** START CODE HERE ***
        m, n = x.shape
        self.theta = np.zeros(n)
        def grad(x,k):
            return np.array([[np.exp(x[index][j]) / (1+np.sum(np.exp(x[index]))) for j in range((k-1))] for index in range(m)])
        def hessian(x,k):
            return np.array([[[( (1+np.sum(np.exp(x[index])))*(j == i)*np.exp(x[index][i])-np.exp(x[index][j])*np.exp(x[index][i])) / (1+np.sum(np.exp(x[index])))**2 for j in range((k-1))] for i in range((k-1))] for index in range(m)])
        k = 2
        T = np.zeros((m,(k-1)))
        for i,obj in enumerate(T):
            if y[i] >= 1:t
                obj[int(y[i])-1] = 1
        # Newton's method
        while True:
            # Save old theta
            theta_old = self.theta.copy()
            t0 = self.theta.reshape(k-1,n)
            eta = np.einsum('ni,mi->mn',t0,x)#np.einsum('mi,mi->m',t0,x)# np.array([[t0[i].T @ x[index] for i in range((k-1))] for index in range(m)])
            logparthessian = hessian(eta,k)
            logpartgrad = grad(eta,k)
            #rowwise products x[i] x[i]^T
            xmatrices = np.einsum('mi,mj->mij',x,x)
            # sum of kronecker products of elements
            lhessian = -np.einsum('mij,mkl->ikjl',logparthessian,xmatrices).reshape(n*(k-1),n*(k-1))
            lhessianinv = np.linalg.inv(lhessian)
            # sum of kronecker products of elements
            lgrad = np.einsum('mi,mj->ij',T-logpartgrad,x).flatten()
            self.theta -= lhessianinv @ lgrad
            error = np.linalg.norm(self.theta-theta_old, ord=1)
            # End training
            if error < self.eps:
                break
        # *** END CODE HERE ***

    def predict(self, x):
        """Make a prediction given new inputs x.

        Args:
            x: Inputs of shape (m, n).

        Returns:
            Outputs of shape (m,).
        """
        # *** START CODE HERE ***
        k=2
        m,n = x.shape
        t0 = self.theta.reshape(k-1,n)
        eta = np.einsum('ni,mi->mn',t0,x)
        return 1 / (1 + np.exp(-eta))

        # *** END CODE HERE ***
main('/home/br/Pictures/ds1_train.csv','/home/br/Pictures/ds1_valid.csv','/home/br/Pictures/CS229/fuckssake2.txt')
