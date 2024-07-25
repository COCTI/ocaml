let rec fibo n = match n with
	| 0 -> 1
	| 1 -> 1
	| n -> fibo (n-1) + fibo (n-2);;