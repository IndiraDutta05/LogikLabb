# LogikLabb

### 1. Vilka bindningar presenteras som resultat?
```
Output: 
T = f(a, a, b),
Y = X, X = a,
Z = b.
```
Here we unify two terms: T = f(a, Y, Z) and T = f(X, X, b) 
The first argument in both terms is a and X, so X = a, The second argument in both terms is Y and X. Since we know from the previous step that X = a, this forces Y = a, The third argument in both terms is Z and b. Thus, Z = b.



### 2. Definiera alltså predikatet remove_duplicates/2! Förklara varför man kan kalla detta predikat för en funktion!

