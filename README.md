# TODO
 - Printowanie stringów: wsparcie + gramatyka

# Parser
JIPP 2015 - Parser

Język prezentuje składnię zbliżoną do C++/Javy 'prawie' zgodną z prezentowaną wcześniej
gramatyką. Obecnie brakuje implementacji dla sensownej widoczności zmiennych, co owocuje
brakiem funkcji i fora. Niemniej jednak mamy wsparcie dla:
- Zmiennych (z przesłanianiem identyfikatorów w blokach)
- Arytmetyki
- Arytmetyki boolowskiej (w interpretacji liczbowej, false == 0, true != 0)
- If + While
- Wyrażenia ternarne (x = bexp ? exp : elseExp)
- print (wypisywanie wyrażeń na standardowe wyjście)
- Dodatkowe operatory przypisania: ++ i -- oraz += *= -= /=
