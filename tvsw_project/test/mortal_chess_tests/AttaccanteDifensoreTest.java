package mortal_chess_tests;

import static org.junit.Assert.*;

import org.junit.Test;

import mortal_chess.Attaccante;
import mortal_chess.AttaccanteDifensore;
import mortal_chess.Difensore;
import mortal_chess.Pedina;

public class AttaccanteDifensoreTest {

	@Test
	public void test() {
		AttaccanteDifensore ad1 = new AttaccanteDifensore('X', 1, 'A', 10, 10);
		assertEquals(ad1.getGiocatore(), 'X');
		
		assertEquals(ad1.getRiga(), 1);
		assertEquals(ad1.getColonna(), 'A');
		ad1.setRiga(2);
		ad1.setColonna('B');
		assertEquals(ad1.getRiga(), 2);
		assertEquals(ad1.getColonna(), 'B');
		
		assertTrue(ad1.isAttaccante());
		assertTrue(ad1.isDifensore());
		assertTrue(ad1.isAttaccanteDifensore());
		
		assertEquals(ad1.getPuntiAttacco(), 10);
		ad1.setPuntiAttacco(5);
		assertEquals(ad1.getPuntiAttacco(), 5);
		
		assertEquals(ad1.getPuntiDifesa(), 10);
		ad1.setPuntiDifesa(5);
		assertEquals(ad1.getPuntiDifesa(), 5);
		
		ad1.muovi(3, 'C');
		assertEquals(ad1.getRiga(), 3);
		assertEquals(ad1.getColonna(), 'C');
		
		AttaccanteDifensore ad2 = new AttaccanteDifensore('O', 8, 'H', 2, 2);
		assertEquals(ad2.getPuntiAttacco(), 2);
		assertEquals(ad2.getPuntiDifesa(), 2);
		
		assertFalse(ad2.attacca());
		assertEquals(ad2.getPuntiAttacco(), 1);
		assertTrue(ad2.attacca());
		assertEquals(ad2.getPuntiAttacco(), 0);
		
		assertFalse(ad2.vieneAttaccata(1));
		assertEquals(ad2.getPuntiDifesa(), 1);
		assertTrue(ad2.vieneAttaccata(1));
		assertEquals(ad2.getPuntiDifesa(), 0);
		
		assertEquals(ad1.toString(), "C3 (AD) - Punti Attacco: 5 - Punti Difesa: 5");
	}
	
	@Test
	public void testUnisciAttaccanteDifensore() {
		
//		public Pedina unisci(Pedina p) {
//	1		Pedina result;
//	2		if (p.isAttaccanteDifensore()) {
//	3			AttaccanteDifensore t = (AttaccanteDifensore) p;
//	4			result = new AttaccanteDifensore(getGiocatore(), getRiga(), getColonna(), getPuntiAttacco() + t.getPuntiAttacco(), getPuntiDifesa() + t.getPuntiDifesa());
//			}
//	5		else if (p.isDifensore()) {
//	6			Difensore t = (Difensore) p;
//	7			result = new AttaccanteDifensore(getGiocatore(), getRiga(), getColonna(), getPuntiAttacco(), getPuntiDifesa() + t.getPuntiDifesa());
//			}
//	8		else {
//	9			Attaccante t = (Attaccante) p;
//	10			result = new AttaccanteDifensore(getGiocatore(), getRiga(), getColonna(), getPuntiAttacco() + t.getPuntiAttacco(), getPuntiDifesa());
//			}
//	11		return result;
//		}
		
		// copertura istruzioni e branch
		
		AttaccanteDifensore ad1 = new AttaccanteDifensore('X', 1, 'A', 2, 1);
		AttaccanteDifensore ad2 = new AttaccanteDifensore('X', 2, 'B', 1, 2);
		Difensore d = new Difensore('X', 4, 'D', 4);
		Attaccante a = new Attaccante('X', 3, 'C', 3);
		
		// copertura istruzioni 1-2-3-4-11
		Pedina p = ad1.unisci(ad2);
		assertEquals(p.getGiocatore(), 'X');
		assertEquals(p.getRiga(), 1);
		assertEquals(p.getColonna(), 'A');
		assertTrue(p instanceof AttaccanteDifensore);
		AttaccanteDifensore ad3 = (AttaccanteDifensore) p;
		assertEquals(ad3.getPuntiAttacco(), 3);
		assertEquals(ad3.getPuntiDifesa(), 3);
		
		// copertura istruzioni 1-2-5-6-7-11
		p = ad1.unisci(d);
		assertEquals(p.getGiocatore(), 'X');
		assertEquals(p.getRiga(), 1);
		assertEquals(p.getColonna(), 'A');
		assertTrue(p instanceof AttaccanteDifensore);
		ad3 = (AttaccanteDifensore) p;
		assertEquals(ad3.getPuntiAttacco(), 2);
		assertEquals(ad3.getPuntiDifesa(), 5);
		
		// copertura istruzioni 1-2-5-8-9-10-11
		p = ad1.unisci(a);
		assertEquals(p.getGiocatore(), 'X');
		assertEquals(p.getRiga(), 1);
		assertEquals(p.getColonna(), 'A');
		assertTrue(p instanceof AttaccanteDifensore);
		ad3 = (AttaccanteDifensore) p;
		assertEquals(ad3.getPuntiAttacco(), 5);
		assertEquals(ad3.getPuntiDifesa(), 1);
		
	}
	
	@Test
	public void testAttaccanteDifensoreEquals() {
		AttaccanteDifensore ad1 = new AttaccanteDifensore('X', 1, 'A', 1, 1);
		assertTrue(ad1.equals(ad1));
		Difensore d = new Difensore('X', '1', 'A');
		assertFalse(ad1.equals(d));
		AttaccanteDifensore ad2 = new AttaccanteDifensore('X', 1, 'A', 1, 1);
		assertTrue(ad1.equals(ad2));
		ad2.setRiga(2);
		assertFalse(ad1.equals(ad2));
		ad2.setRiga(1);
		assertTrue(ad1.equals(ad2));
		ad2.setColonna('B');
		assertFalse(ad1.equals(ad2));
		ad2.setColonna('A');
		assertTrue(ad1.equals(ad2));
		ad2.setPuntiAttacco(2);
		assertFalse(ad1.equals(ad2));
		ad2.setPuntiAttacco(1);
		assertTrue(ad1.equals(ad2));
		ad2.setPuntiDifesa(2);
		assertFalse(ad1.equals(ad2));
		ad2.setPuntiDifesa(1);
		assertTrue(ad1.equals(ad2));
	}

}
