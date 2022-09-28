
asm MortalChess

import StandardLibrary
import CTLlibrary
import LTLlibrary

signature:

	// DOMAINS
	
	domain Giocatore subsetof Integer
	domain PuntiGiocatore subsetof Integer
	domain Mossa subsetof Integer
	domain Riga subsetof Integer
	domain Colonna subsetof Integer
	enum domain Tipologia = {ATTACCANTE, DIFENSORE, ATTACCANTEDIFENSORE, VUOTA}
	domain PuntiPedina subsetof Integer
	
	// FUNCTIONS
	
	controlled turno: Giocatore
	controlled puntiGiocatore: Giocatore -> PuntiGiocatore
	controlled giocatorePedina: Prod(Riga, Colonna) -> Giocatore
	controlled tipologiaPedina: Prod(Riga, Colonna) -> Tipologia
	controlled puntiAttacco: Prod(Riga, Colonna) -> PuntiPedina
	controlled puntiDifesa: Prod(Riga, Colonna) -> PuntiPedina
	
	monitored mossa: Mossa
	monitored riga1: Riga
	monitored colonna1: Colonna
	monitored riga2: Riga
	monitored colonna2: Colonna
	monitored tipologia: Tipologia
	
	derived partitaFinita: Boolean
	derived vincitore: Giocatore
	derived avversario: Giocatore -> Giocatore
	
	derived celleAdiacenti: Prod(Riga, Colonna, Riga, Colonna) -> Boolean
	derived pedinaPosizionabile: Prod(Giocatore, Riga, Colonna) -> Boolean
	derived pedinaMovibile: Prod(Giocatore, Riga, Colonna, Riga, Colonna) -> Boolean
	derived pedineUnibili: Prod(Giocatore, Riga, Colonna, Riga, Colonna) -> Boolean
	derived pedinaAttaccantePedina: Prod(Giocatore, Riga, Colonna, Riga, Colonna) -> Boolean
	derived pedinaAttaccanteAvversario: Prod(Giocatore, Riga, Colonna) -> Boolean

definitions:

	// DOMAIN DEFINITIONS
	
	domain Giocatore = {0:2}
	domain PuntiGiocatore = {0:10}
	domain Mossa = {1:5}
	domain Riga = {1:8}
	domain Colonna = {1:8}
	domain PuntiPedina = {0:100}

	// FUNCTION DEFINITIONS
	
	function partitaFinita =
		(puntiGiocatore(1) = 0 or puntiGiocatore(2) = 0)
	
	function vincitore =
		if puntiGiocatore(1) = 0 then
			2
		else
			if puntiGiocatore(2) = 0 then
				1
			else
				0
			endif
		endif
	
	function avversario($g in Giocatore) =
		if $g = 1 then
			2
		else
			if $g = 2 then
				1
			else
				0
			endif
		endif
	
	
	function celleAdiacenti($r1 in Riga, $c1 in Colonna, $r2 in Riga, $c2 in Colonna) =
		if ($r1 = $r2 and $c1 = $c2) then false 
		else if ($c1 = 1 and $c2 != 1 and $c2 != 2) then false
			else if ($c1 = 8 and $c2 != 8 and $c2 != 7) then false 
				else if ($c1 != 1 and $c1 != 8 and $c1 != $c2 and $c2 != ($c1-1) and $c2 != ($c1+1)) then false
					else if ($r1 = 1 and $r2 != 1 and $r2 != 2) then false
						else if ($r1 = 8 and $r2 != 8 and $r2 != 7) then false
							else if ($r1 != 1 and $r1 != 8 and $r1 != $r2 and $r2 != ($r1-1) and $r2 != ($r1+1)) then false
								else true
								endif
							endif
						endif
					endif
				endif
			endif
		endif
	
	
	function pedinaPosizionabile($g in Giocatore, $r in Riga, $c in Colonna) =
		( tipologiaPedina($r, $c) = VUOTA and ( ($g = 1 and $c = 1) or ($g = 2 and $c = 8) ) )
	
	function pedinaMovibile($g in Giocatore, $r1 in Riga, $c1 in Colonna, $r2 in Riga, $c2 in Colonna) =
		( giocatorePedina($r1, $c1) = $g and tipologiaPedina($r2, $c2) = VUOTA and celleAdiacenti($r1, $c1, $r2, $c2) )
	
	function pedineUnibili($g in Giocatore, $r1 in Riga, $c1 in Colonna, $r2 in Riga, $c2 in Colonna) =
		( giocatorePedina($r1, $c1) = $g and giocatorePedina($r2, $c2) = $g and celleAdiacenti($r1, $c1, $r2, $c2) )
	
	function pedinaAttaccantePedina($g in Giocatore, $r1 in Riga, $c1 in Colonna, $r2 in Riga, $c2 in Colonna) =
		( giocatorePedina($r1, $c1) = $g and giocatorePedina($r2, $c2) = avversario($g) and
		  puntiAttacco($r1, $c1) > 0 and celleAdiacenti($r1, $c1, $r2, $c2)	)
	
	function pedinaAttaccanteAvversario($g in Giocatore, $r in Riga, $c in Colonna) =
		( giocatorePedina($r, $c) = $g and puntiAttacco($r, $c) > 0 and ( ($g = 1 and $c = 8) or ($g = 2 and $c = 1) ) )
	
	// RULE DEFINITIONS
	
	rule r_cambiaTurno($g in Giocatore) =
		turno := avversario($g)
	
	rule r_eliminaPedina($r in Riga, $c in Colonna) =
		par
			giocatorePedina($r, $c) := 0
			tipologiaPedina($r, $c) := VUOTA
			puntiAttacco($r, $c) := 0
			puntiDifesa($r, $c) := 0
		endpar
	
	rule r_posizionaPedina($g in Giocatore, $r in Riga, $c in Colonna, $t in Tipologia) =
		par
			giocatorePedina($r, $c) := $g
			tipologiaPedina($r, $c) := $t
			if $t = ATTACCANTE then
				puntiAttacco($r, $c) := 1
			else
				puntiDifesa($r, $c) := 1
			endif
			r_cambiaTurno[$g]
		endpar
	
	rule r_muoviPedina($g in Giocatore, $r1 in Riga, $c1 in Colonna, $r2 in Riga, $c2 in Colonna) =
		par
			giocatorePedina($r2, $c2) := giocatorePedina($r1, $c1)
			tipologiaPedina($r2, $c2) := tipologiaPedina($r1, $c1)
			puntiAttacco($r2, $c2) := puntiAttacco($r1, $c1)
			puntiDifesa($r2, $c2) := puntiDifesa($r1, $c1)
			r_eliminaPedina[$r1, $c1]
			r_cambiaTurno[$g]
		endpar
	
	rule r_unisciPedine($g in Giocatore, $r1 in Riga, $c1 in Colonna, $r2 in Riga, $c2 in Colonna) =
		par
			if tipologiaPedina($r1, $c1) != tipologiaPedina($r2, $c2) then
				tipologiaPedina($r1, $c1) := ATTACCANTEDIFENSORE
			endif
			puntiAttacco($r1, $c1) := puntiAttacco($r1, $c1) + puntiAttacco($r2, $c2)
			puntiDifesa($r1, $c1) := puntiDifesa($r1, $c1) + puntiDifesa($r2, $c2)
			r_eliminaPedina[$r2, $c2]
			r_cambiaTurno[$g]
		endpar
	
	rule r_attaccaPedina($g in Giocatore, $r1 in Riga, $c1 in Colonna, $r2 in Riga, $c2 in Colonna) =
		par
			if puntiDifesa($r2, $c2) <= puntiAttacco($r1, $c1) then
				r_eliminaPedina[$r2, $c2]
			else
				puntiDifesa($r2, $c2) := puntiDifesa($r2, $c2) - puntiAttacco($r1, $c1)
			endif
			if puntiAttacco($r1, $c1) = 1 then
				r_eliminaPedina[$r1, $c1]
			else
				puntiAttacco($r1, $c1) := puntiAttacco($r1, $c1) - 1
			endif
			r_cambiaTurno[$g]
		endpar
	
	rule r_attaccaAvversario($g in Giocatore, $r in Riga, $c in Colonna) =
		par
			let ($a = avversario($g)) in
				if puntiGiocatore($a) <= puntiAttacco($r, $c) then
					puntiGiocatore($a) := 0
				else
					puntiGiocatore($a) := puntiGiocatore($a) - puntiAttacco($r, $c)
				endif
			endlet
			if puntiAttacco($r, $c) = 1 then
				r_eliminaPedina[$r, $c]
			else
				puntiAttacco($r, $c) := puntiAttacco($r, $c) - 1
			endif
			r_cambiaTurno[$g]
		endpar
	
	// INVARIANTS
	
	
	// Proprietà 1: entrambi i giocatori possono vincere
	CTLSPEC (forall $g in Giocatore with $g != 0 and ef(vincitore = $g))
	// Proprietà 2: i punti dei due giocatori non possono mai essere a 0 contemporaneamente
	CTLSPEC ag(not (puntiGiocatore(1) = 0 and puntiGiocatore(2) = 0))
	// Proprietà 3: il giocatore 1 non può sempre schierare una pedina
	CTLSPEC ef( not (exist $r in Riga, $c in Colonna with (not partitaFinita) and pedinaPosizionabile(1, $r, $c)))
	// Proprietà 4: se il giocatore 1 non ha pedine schierate, non può muovere una pedina
	CTLSPEC ag( (forall $r in Riga, $c in Colonna with giocatorePedina($r, $c) != 1) implies
		(forall $r1 in Riga, $c1 in Colonna, $r2 in Riga, $c2 in Colonna with (not (pedinaMovibile(1, $r1, $c1, $r2, $c2))) )
	)
	// Proprietà 5: se il giocatore 1 attacca l'avversario con una pedina attaccante nella cella H8 con punti attacco = 5
	// e l'avversario ha 10 punti, successivamente quest'ultimo avrà 5
	CTLSPEC ag( (turno=1 and (not partitaFinita) and giocatorePedina(8,8) = 1 and tipologiaPedina(8,8) = ATTACCANTE and puntiAttacco(8,8) = 5 and mossa = 5 and puntiGiocatore(2) = 10)
		implies ax(puntiGiocatore(2) = 5)
	)
	// Proprietà 6: 
	CTLSPEC ag( turno=1 and (not partitaFinita) and mossa = 4 and (exist $r1 in Riga, $c1 in Colonna, $r2 in Riga, $c2 in Colonna with pedinaAttaccantePedina(1, $r1, $c1, $r2, $c2))
		implies ax(turno=2 and (not partitaFinita))
	)
	
	
	
	// MAIN RULE
	
	main rule r_Main =
		if (not partitaFinita) then
			let ($g = turno, $m = mossa, $r1 = riga1, $c1 = colonna1, $r2 = riga2, $c2 = colonna2, $t = tipologia) in
				switch $m
					case 1:
						if pedinaPosizionabile($g, $r1, $c1) then r_posizionaPedina[$g, $r1, $c1, $t] endif
					case 2:
						if pedinaMovibile($g, $r1, $c1, $r2, $c2) then r_muoviPedina[$g, $r1, $c1, $r2, $c2] endif
					case 3:
						if pedineUnibili($g, $r1, $c1, $r2, $c2) then r_unisciPedine[$g, $r1, $c1, $r2, $c2] endif
					case 4:
						if pedinaAttaccantePedina($g, $r1, $c1, $r2, $c2) then r_attaccaPedina[$g, $r1, $c1, $r2, $c2] endif
					case 5:
						if pedinaAttaccanteAvversario($g, $r1, $c1) then r_attaccaAvversario[$g, $r1, $c1] endif
				endswitch
			endlet
		endif

// INITIAL STATE
default init s0:
	function turno = 1
	function puntiGiocatore($g in Giocatore) = 10
	function giocatorePedina($r in Riga, $c in Colonna) = 0
	function tipologiaPedina($r in Riga, $c in Colonna) = VUOTA
	function puntiAttacco($r in Riga, $c in Colonna) = 0
	function puntiDifesa($r in Riga, $c in Colonna) = 0
