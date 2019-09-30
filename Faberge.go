package main

import (
	"fmt"
	"math/big"
)

var table [20000][20000]*big.Int

func Height(n, m *big.Int) *big.Int {

	for i := 0; i < 2000; i++ {
		table[0][i] = big.NewInt(0)
		table[i][0] = big.NewInt(0)
		table[i][1] = big.NewInt(1)
		table[1][i] = big.NewInt(int64(i))
	}

	one := big.NewInt(1)
	ni := n.Int64()
	mi := m.Int64()
	var i, j int64
	for i = 2; i <= ni; i++ {
		for j = 2; j <= mi; j++ {
			table[i][j] = big.NewInt(0)
			table[i][j].Add(table[i-1][j-1], table[i][j-1])
			table[i][j].Add(table[i][j], one)
		}
	}
	return table[n.Int64()][m.Int64()] // do it!
}

func main() {
	n := big.NewInt(2)
	m := big.NewInt(14)

	fmt.Println("Resultado pa:", n, m, Height(n, m))
}
