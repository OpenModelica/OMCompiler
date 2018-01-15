// Van der Pol model

model VanDerPol  "Van der Pol oscillator model"
  Real x(start = 1, fixed = true);
  Real y(start = 1, fixed = true);
  parameter Real lambda = 0.3;
equation
  der(x) = y;
  der(y) = - x + lambda*(1 - x*x)*y;
end VanDerPol;
