package mortal_chess_tests;

import static org.junit.Assert.*;

import org.junit.Test;

import mortal_chess.Attaccante;
import mortal_chess.AttaccanteDifensore;
import mortal_chess.Difensore;
import mortal_chess.Pedina;

public class AttaccanteTest {

	@Test
	public void testAttaccante() {
		Attaccante a1 = new Attaccante('X', 1, 'A', 10);
		assertEquals(a1.getGiocatore(), 'X');
		
		assertEquals(a1.getRiga(), 1);
		assertEquals(a1.getColonna(), 'A');
		a1.setRiga(2);
		a1.setColonna('B');
		assertEquals(a1.getRiga(), 2);
		assertEquals(a1.getColonna(), 'B');
		
		assertTrue(a1.isAttaccante());
		assertFalse(a1.isDifensore());
		assertFalse(a1.isAttaccanteDifensore());
		
		assertEquals(a1.getPuntiAttacco(), 10);
		a1.setPuntiAttacco(5);
		assertEquals(a1.getPuntiAttacco(), 5);
		
		Attaccante a2 = new Attaccante('O', 8, 'H');
		assertEquals(a2.getPuntiAttacco(), 1);
		
		a1.muovi(3, 'C');
		assertEquals(a1.getRiga(), 3);
		assertEquals(a1.getColonna(), 'C');
		
		assertFalse(a1.attacca());
		assertEquals(a1.getPuntiAttacco(), 4);
		assertTrue(a2.attacca());
		assertEquals(a2.getPuntiAttacco(), 0);
		
		assertTrue(a1.vieneAttaccata(1));
		assertTrue(a2.vieneAttaccata(2));
		
		assertEquals(a1.toString(), "C3 (A) - Punti Attacco: 4");
	}
	
	@Test
	public void testUnisciAttaccante() {
		
//		public Pedina unisci(Pedina p) {
//	1		Pedina result;
//	2		if (p.isAttaccanteDifensore()) {
//	3			AttaccanteDifensore t = (AttaccanteDifensore) p;
//	4			result = new AttaccanteDifensore(getGiocatore(), getRiga(), getColonna(), getPuntiAttacco() + t.getPuntiAttacco(), t.getPuntiDifesa());
//			}
//	5		else if (p.isDifensore()) {
//	6			Difensore t = (Difensore) p;
//	7			result = new AttaccanteDifensore(getGiocatore(), getRiga(), getColonna(), getPuntiAttacco(), t.getPuntiDifesa());
//			}
//	8		else {
//	9			Attaccante t = (Attaccante) p;
//	10			result = new Attaccante(getGiocatore(), getRiga(), getColonna(), getPuntiAttacco() + t.getPuntiAttacco());
//			}
//	11		return result;
//		}
		
		// copertura istruzioni e branch
		
		Attaccante a1 = new Attaccante('X', 1, 'A');
		AttaccanteDifensore ad1 = new AttaccanteDifensore('X', 2, 'B', 1, 2);
		Difensore d = new Difensore('X', 4, 'D', 4);
		Attaccante a2 = new Attaccante('X', 3, 'C', 3);
		
		// copertura istruzioni 1-2-3-4-11
		Pedina p = a1.unisci(ad1);
		assertEquals(p.getGiocatore(), 'X');
		assertEquals(p.getRiga(), 1);
		assertEquals(p.getColonna(), 'A');
		assertTrue(p instanceof AttaccanteDifensore);
		AttaccanteDifensore ad2 = (AttaccanteDifensore) p;
		assertEquals(ad2.getPuntiAttacco(), 2);
		assertEquals(ad2.getPuntiDifesa(), 2);
		
		// copertura istruzioni 1-2-5-6-7-11
		p = a1.unisci(d);
		assertEquals(p.getGiocatore(), 'X');
		assertEquals(p.getRiga(), 1);
		assertEquals(p.getColonna(), 'A');
		assertTrue(p instanceof AttaccanteDifensore);
		ad2 = (AttaccanteDifensore) p;
		assertEquals(ad2.getPuntiAttacco(), 1);
		assertEquals(ad2.getPuntiDifesa(), 4);
		
		// copertura istruzioni 1-2-5-8-9-10-11
		p = a1.unisci(a2);
		assertEquals(p.getGiocatore(), 'X');
		assertEquals(p.getRiga(), 1);
		assertEquals(p.getColonna(), 'A');
		assertTrue(p instanceof Attaccante);
		Attaccante a3 = (Attaccante) p;
		assertEquals(a3.getPuntiAttacco(), 4);
		
	}
	
	@Test
	public void testAttaccanteEquals() {
		Attaccante a1 = new Attaccante('X', 1, 'A');
		assertTrue(a1.equals(a1));
		Difensore d = new Difensore('X', 1, 'A');
		assertFalse(a1.equals(d));
		Attaccante a2 = new Attaccante('X', 1, 'A');
		assertTrue(a1.equals(a2));
		a2.setRiga(2);
		assertFalse(a1.equals(a2));
		a2.setRiga(1);
		assertTrue(a1.equals(a2));
		a2.setColonna('B');
		assertFalse(a1.equals(a2));
		a2.setColonna('A');
		assertTrue(a1.equals(a2));
		a2.setPuntiAttacco(2);
		assertFalse(a1.equals(a2));
		a2.setPuntiAttacco(1);
		assertTrue(a1.equals(a2));
	}
	
}
