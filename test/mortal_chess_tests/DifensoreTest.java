package mortal_chess_tests;

import static org.junit.Assert.*;

import org.junit.Test;

import mortal_chess.Attaccante;
import mortal_chess.AttaccanteDifensore;
import mortal_chess.Difensore;
import mortal_chess.Pedina;

public class DifensoreTest {

	@Test
	public void testDifensore() {
		Difensore d1 = new Difensore('X', 1, 'A', 10);
		assertEquals(d1.getGiocatore(), 'X');
		
		assertEquals(d1.getRiga(), 1);
		assertEquals(d1.getColonna(), 'A');
		d1.setRiga(2);
		d1.setColonna('B');
		assertEquals(d1.getRiga(), 2);
		assertEquals(d1.getColonna(), 'B');
		
		assertFalse(d1.isAttaccante());
		assertTrue(d1.isDifensore());
		assertFalse(d1.isAttaccanteDifensore());
		
		assertEquals(d1.getPuntiDifesa(), 10);
		d1.setPuntiDifesa(5);
		assertEquals(d1.getPuntiDifesa(), 5);
		
		Difensore d2 = new Difensore('O', 8, 'H');
		assertEquals(d2.getPuntiDifesa(), 1);
		
		d1.muovi(3, 'C');
		assertEquals(d1.getRiga(), 3);
		assertEquals(d1.getColonna(), 'C');
		
		assertFalse(d1.vieneAttaccata(1));
		assertEquals(d1.getPuntiDifesa(), 4);
		assertTrue(d1.vieneAttaccata(4));
		assertEquals(d1.getPuntiDifesa(), 0);
		
		assertEquals(d1.toString(), "C3 (D) - Punti Difesa: 0");
	}
	
	@Test
	public void testUnisciDifensore() {
		
//		public Pedina unisci(Pedina p) {
//	1		Pedina result;
//	2		if (p.isAttaccanteDifensore()) {
//	3			AttaccanteDifensore t = (AttaccanteDifensore) p;
//	4			result = new AttaccanteDifensore(getGiocatore(), getRiga(), getColonna(), t.getPuntiAttacco(), getPuntiDifesa() + t.getPuntiDifesa());
//			}
//	5		else if (p.isDifensore()) {
//	6			Difensore t = (Difensore) p;
//	7			result = new Difensore(getGiocatore(), getRiga(), getColonna(), getPuntiDifesa() + t.getPuntiDifesa());
//			}
//	8		else {
//	9			Attaccante t = (Attaccante) p;
//	10			result = new AttaccanteDifensore(getGiocatore(), getRiga(), getColonna(), t.getPuntiAttacco(), getPuntiDifesa());
//			}
//	11		return result;
//		}
		
		// copertura istruzioni e branch
		
		Difensore d1 = new Difensore('X', 1, 'A');
		AttaccanteDifensore ad1 = new AttaccanteDifensore('X', 2, 'B', 1, 2);
		Difensore d2 = new Difensore('X', 4, 'D', 4);
		Attaccante a = new Attaccante('X', 3, 'C', 3);
		
		// copertura istruzioni 1-2-3-4-11
		Pedina p = d1.unisci(ad1);
		assertEquals(p.getGiocatore(), 'X');
		assertEquals(p.getRiga(), 1);
		assertEquals(p.getColonna(), 'A');
		assertTrue(p instanceof AttaccanteDifensore);
		AttaccanteDifensore ad2 = (AttaccanteDifensore) p;
		assertEquals(ad2.getPuntiAttacco(), 1);
		assertEquals(ad2.getPuntiDifesa(), 3);
		
		// copertura istruzioni 1-2-5-6-7-11
		p = d1.unisci(d2);
		assertEquals(p.getGiocatore(), 'X');
		assertEquals(p.getRiga(), 1);
		assertEquals(p.getColonna(), 'A');
		assertTrue(p instanceof Difensore);
		Difensore d3 = (Difensore) p;
		assertEquals(d3.getPuntiDifesa(), 5);
		
		// copertura istruzioni 1-2-5-8-9-10-11
		p = d1.unisci(a);
		assertEquals(p.getGiocatore(), 'X');
		assertEquals(p.getRiga(), 1);
		assertEquals(p.getColonna(), 'A');
		assertTrue(p instanceof AttaccanteDifensore);
		ad2 = (AttaccanteDifensore) p;
		assertEquals(ad2.getPuntiAttacco(), 3);
		assertEquals(ad2.getPuntiDifesa(), 1);
		
	}
	
	@Test
	public void testDifensoreEquals() {
		Difensore d1 = new Difensore('X', 1, 'A');
		assertTrue(d1.equals(d1));
		Attaccante a = new Attaccante('X', 1, 'A');
		assertFalse(d1.equals(a));
		Difensore d2 = new Difensore('X', 1, 'A');
		assertTrue(d1.equals(d2));
		d2.setRiga(2);
		assertFalse(d1.equals(d2));
		d2.setRiga(1);
		assertTrue(d1.equals(d2));
		d2.setColonna('B');
		assertFalse(d1.equals(d2));
		d2.setColonna('A');
		assertTrue(d1.equals(d2));
		d2.setPuntiDifesa(2);
		assertFalse(d1.equals(d2));
		d2.setPuntiDifesa(1);
		assertTrue(d1.equals(d2));
	}

}
