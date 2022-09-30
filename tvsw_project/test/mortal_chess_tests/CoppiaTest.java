package mortal_chess_tests;

import static org.junit.Assert.*;

import org.junit.Test;

import mortal_chess.Coppia;

public class CoppiaTest {

	@Test
	public void testCoppia() {
		Integer i = 1;
		Character c = 'A';
		Coppia<Integer, Character> coppia = new Coppia<>(i, c);
		assertTrue(coppia.getPrimo() instanceof Integer);
		assertTrue(coppia.getSecondo() instanceof Character);
		assertEquals(coppia.getPrimo(), Integer.valueOf(1));
		assertEquals(coppia.getSecondo(), new Character('A'));
		
		i = 2;
		c = 'B';
		coppia.setPrimo(i);
		coppia.setSecondo(c);
		assertEquals(coppia.getPrimo(), Integer.valueOf(2));
		assertEquals(coppia.getSecondo(), new Character('B'));
	}
	
	@Test
	public void testEqualsCoppia() {
		Coppia<Integer, Character> c1 = new Coppia<Integer, Character>(Integer.valueOf(1), new Character('A'));
		Coppia<Integer, Character> c2 = new Coppia<Integer, Character>(Integer.valueOf(2), new Character('A'));
		Coppia<Integer, Character> c3 = new Coppia<Integer, Character>(Integer.valueOf(1), new Character('B'));
		assertTrue(c1.equals(c1));
		assertFalse(c1.equals(c2));
		assertFalse(c1.equals(c3));
		Object o = new Object();
		assertFalse(c1.equals(o));
	}

}
