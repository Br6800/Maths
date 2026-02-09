import numpy as np
import util
np.set_printoptions(threshold=np.inf)
import matplotlib.pyplot as plt

from linear_model import LinearModel


def main(train_path, eval_path, pred_path):
    """Problem 1(b): Logistic regression with Newton's Method.

    Args:
        train_path: Path to CSV file containing dataset for training.
        eval_path: Path to CSV file containing dataset for evaluation.
        pred_path: Path to save predictions.
    """
    """
    x_train, y_train = util.load_dataset(train_path, add_intercept=True)
    # *** START CODE HERE ***
    x_eval, y_eval = util.load_dataset(eval_path, add_intercept=True)
    model = LogisticRegression(eps=1e-5)
    model.fit(x_train,y_train)
    y_pred = model.predict(x_eval)
    util.plot(x_train, y_train, model.theta, 'output/p01b_2total.png')
    np.savetxt(pred_path, y_pred, fmt='%d')
    """
    def add_intercept(X):
        return np.hstack([np.ones((X.shape[0], 1)),X])

    model = LogisticRegression(eps=1e-5)
    X,y = util.load_dataset(train_path, add_intercept=True)
    # Train
    model.fit(X,y)

    # ----- Decision region plot -----
    x_min, x_max = X[:,1].min()-.3*abs(X[:,1].min()), X[:,1].max()+.3*abs(X[:,1].max())
    y_min, y_max = X[:,2].min()-.3*abs(X[:,2].min()), X[:,2].max()+.3*abs(X[:,1].max())
    xx, yy = np.meshgrid(np.linspace(x_min,x_max,200), np.linspace(y_min,y_max,200))

    grid = np.c_[xx.ravel(), yy.ravel()]
    grid_i = add_intercept(grid)

    Z = model.predict(grid_i).reshape(xx.shape)

    plt.figure()
    plt.contourf(xx, yy, Z, alpha=0.3)
    plt.scatter(X[:,1], X[:,2], c=y)
    plt.title(f"Softmax Regression with {len(set(y))} categories and Intercept")
    plt.xlabel("x1")
    plt.ylabel("x2")
    plt.legend()
    plt.show()


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
        m, n = x.shape
        def grad(var,k):
            return np.array([[np.exp(var[index][j]) / (1+np.sum(np.exp(var[index]))) for j in range((k-1))] for index in range(m)])
        def hessian(var,k):
            return np.array([[[( (1+np.sum(np.exp(var[index])))*(j == i)*np.exp(var[index][i])-np.exp(var[index][j])*np.exp(var[index][i])) / (1+np.sum(np.exp(var[index])))**2 for j in range((k-1))] for i in range((k-1))] for index in range(m)])
        k = 3
        self.theta = np.zeros((k-1)*n)
        T = np.zeros((m,(k-1)))
        for i,obj in enumerate(T):
            if int(y[i]) < k-1:
                obj[int(y[i])] = 1


        # Newton's method
        for i in range(800):
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
            print("error",error)

            if error < self.eps:
                break


    def predict(self, x):
        """Make a prediction given new inputs x.

        Args:
            x: Inputs of shape (m, n).

        Returns:
            Outputs of shape (m,).
        """

        k=3
        m,n = x.shape
        t0 = self.theta.reshape(k-1,n)
        eta = np.einsum('ni,mi->mn',t0,x)
        exp_eta = np.exp(eta)
        exp_eta_sum = np.sum(exp_eta, axis=1, keepdims=True)
        return np.argmax(np.hstack([exp_eta / (1 + exp_eta_sum),1 / (1+ exp_eta_sum)]),axis=1)


main('ds1_train.csv','ds1_valid.csv','output_cat.txt')
