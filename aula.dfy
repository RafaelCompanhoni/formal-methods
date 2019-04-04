// PASSO A PASSO
//  definir a assinatura do método
//  definir quais são as pré-condições (requires)
//  definir as pós-condições (ensures)
//  implementar

method Double(x:int) returns (r:int)
ensures r == 2*x
{
    r := 2*x;
}

// demonstra como utilizar métodos previamente definidos

method Triple(x:int) returns (r:int)
ensures r == 3*x
{
    var y := Double(x);
    r := y + x;
}

// Retorna a soma das entradas e o maior valor (máximo) dentre elas
method SumMax(x:int, y:int) returns (s:int, m:int)
requires x >= 0 && y >= 0
ensures s == x + y          // pós-condição em relação à soma: garante que s será a soma
ensures x <= m && y <= m    // pós-condição em relação ao máximo: garante que m será um valor entre x e y
ensures m == x || m == y    // pós-condição em relação ao máximo: garante que m será x ou y
{
    s := x + y;
    if x < y
    {
        m := y;
    } else 
    {
        m := x;
    }
}

function Fib(n: nat): nat
decreases n
{
  if n < 2 then n else Fib(n-2) + Fib(n-1)
}

method ComputaFib(n:nat) returns (x:nat)
ensures x == Fib(n)
{
    x := 0;
    var y := 1;
    var i := 0;

    while i < n
    invariant 0 <= i <= n
    invariant x == Fib(i) && y == Fib(i + 1)
    {
        x, y := y, x + y; // multiplos assignments na mesma linha -- x = y e y = x + y
        i := i + 1;   
    }
}
