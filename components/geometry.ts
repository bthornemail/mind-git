
// Zero Polynomial Function
type ZeroPolynomialFunction<X,A> = (x: X) => {
    // A zero polynomial function is of the form f(x) = 0, yes, it just contains just 0 and no other term or variable. 
    // Since f(x) = a constant here, it is a constant function.
    a: [[a:A,x: X]]
};

// Linear Polynomial Function
type LinearPolynomialFunction<X,A,B> = (x: X) => {
    // A linear polynomial function has a degree 1. 
    // It is of the form f(x) = ax + b. 
    a: [[a:A,x: X]],
    b: [[b: B]]
};

// Quadratic Polynomial Function
type QuadraticPolynomialFunction<X,A,B,C> = (x: X) => {
    // A quadratic polynomial function has a degree 2. 
    // It is of the form f(x) = ax2 + bx + c.
    a: [[a:A,x: X],[a:A,x: X]],
    b: [[b: B,x: X]],
    c: [[c: C]]
};

// Cubic Polynomial Function
type CubicPolynomialFunction<X,A,B,C,D> = (x: X) => {
    // A cubic polynomial function has a degree 3. 
    // It is of the form f(x) = ax3 + bx2 + cx + d.
    a: [[a:A,x: X],[a:A,x: X],[a:A,x: X]],
    b: [[b: B,x: X],[b: B,x: X]],
    c: [[c: C,x: X]]
    d: [[d: D]]
};

type PolymialFunction<X,D> = (x: X) => {
    // Monomials are polynomials that contain only one term. Examples: 15x2, 3b, and 12y4
    d: [[d: D]]
};
type MonomialFunction<X,A> = (x: X) => {
    // Monomials are polynomials that contain only one term. Examples: 15x2, 3b, and 12y4
    a: [[a: A,x: X]]
};
type BinomialFunction<X,A,B> = (x: X) => {
    // Binomials are polynomials that contain only two terms. Examples: x + y, 4x – 7, and 9x + 2
    a: [[a: A,x: X],[a: A,x: X]]
    b: [[b: B,x: X]]
};
type TrinomialFunction<X,A,B,C> = (x: X) => {
    // Trinomials are polynomials that contain only three terms. Examples: x3 – 3 + 5x, z4 + 45 + 3z, and x2 – 12x + 15
    a: [[a: A,x: X],[a: A,x: X],[a: A,x: X]]
    b: [[b: B,x: X],[b: B,x: X]]
    c: [[c: C,x: X]]
};
type TERM = any;
type EXPONENT = any;
type OPERATOR = any;
type CONSTANT = any;
type EXPRESSION = any;

/*

Important Notes on Polynomial Functions:

Here is a list of a few points that should be remembered while studying polynomial functions:

The degree of the polynomial function is determined by the highest power of the variable it is raised to.
Constant functions are polynomial functions of degree 0.
Linear Functions are polynomial functions of degree 1.
Quadratic Functions are polynomial functions of degree 2.
Cubic Functions are polynomial functions of degree 3

*/
export { ZeroPolynomialFunction,LinearPolynomialFunction, QuadraticPolynomialFunction,CubicPolynomialFunction}
export default function getGeometry(){}