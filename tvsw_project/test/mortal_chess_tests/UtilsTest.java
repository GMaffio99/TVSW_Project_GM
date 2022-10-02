package mortal_chess_tests;

import static org.junit.Assert.*;

import java.util.ArrayList;

import org.junit.Test;
import org.junit.runner.RunWith;

import junitparams.JUnitParamsRunner;
import junitparams.Parameters;
import mortal_chess.Coppia;

import static mortal_chess.TavoloUtils.*;

@RunWith(JUnitParamsRunner.class)
public class UtilsTest {

	@Test
	@Parameters({"1, true", "100, true", "-3, true", "0.1, false", "1O, false", "ABC, false", " , false"})
	public void testIsInteger(String s, boolean b) {
		assertEquals(isInteger(s), b);
	}
	
	@Test
	@Parameters({"0, 0", "1, 1", "2, 2", "3, 3", "4, 4", "5, 5", "6, 6", "7, 7", "8, 8", "9, 0"})
	public void testCharToInt(char c, int i) {
		assertEquals(charToInt(c), i);
	}
	
	@Test
	@Parameters({"0, 0", "1, 1", "2, 2", "3, 3", "4, 4", "5, 5", "6, 6", "7, 7", "8, 8", "9, 0"})
	public void testIntToChar(int i, char c) {
		assertEquals(intToChar(i), c);
	}
	
	@Test
	@Parameters({"1, A, 0", "2, B, 9", "3, C, 18", "4, D, 27", "5, E, 36", "6, F, 45", "7, G, 54", "8, H, 63", "9, I, -1"})
	public void testGetIndexWithCharRow(char r, char c, int index) {
		assertEquals(getIndex(r, c), index);
	}
	
	@Test
	@Parameters({"1, A, 0", "2, B, 9", "3, C, 18", "4, D, 27", "5, E, 36", "6, F, 45", "7, G, 54", "8, H, 63", "9, I, -1"})
	public void testGetIndexWithIntRow(int r, char c, int index) {
		assertEquals(getIndex(r, c), index);
	}
	
	@Test
	public void testGetCelleAdiacenti() {
		ArrayList<Coppia<Integer, Character>> celleAdiacenti = getCelleAdiacenti('2', 'B', false);
		assertEquals(celleAdiacenti.size(), 8);
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(1, 'A')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(1, 'B')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(1, 'C')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(2, 'A')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(2, 'C')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(3, 'A')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(3, 'B')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(3, 'C')));
		celleAdiacenti = getCelleAdiacenti('2', 'B', true);
		assertEquals(celleAdiacenti.size(), 4);
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(1, 'B')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(2, 'A')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(2, 'C')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(3, 'B')));
		celleAdiacenti = getCelleAdiacenti('8', 'H', false);
		assertEquals(celleAdiacenti.size(), 3);
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(7, 'G')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(7, 'H')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(8, 'G')));
		celleAdiacenti = getCelleAdiacenti('8', 'H', true);
		assertEquals(celleAdiacenti.size(), 2);
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(7, 'H')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(8, 'G')));
		celleAdiacenti = getCelleAdiacenti('1', 'C', true);
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(1, 'B')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(2, 'C')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(1, 'D')));
		celleAdiacenti = getCelleAdiacenti('1', 'D', true);
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(1, 'C')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(2, 'D')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(1, 'E')));
		celleAdiacenti = getCelleAdiacenti('1', 'E', true);
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(1, 'D')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(2, 'E')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(1, 'F')));
		celleAdiacenti = getCelleAdiacenti('1', 'F', true);
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(1, 'E')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(2, 'F')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(1, 'G')));
		celleAdiacenti = getCelleAdiacenti('8', 'G', true);
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(8, 'F')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(7, 'G')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(8, 'H')));
		celleAdiacenti = getCelleAdiacenti('9', 'I', true);
		assertNull(celleAdiacenti);
	}
	
}
