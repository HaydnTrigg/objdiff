/* objdiff logical diff test: single instructions moved past others (base side).
   Built with MSVC 6.0: cl /nologo /c /O2 base.c */
extern void g(void);
extern float k;

/* `mov ecx, esi` after the x87 ops: the base sets it up before them */
__declspec(naked) void moved(void) {
    __asm {
        mov esi, ecx
        call g
        mov ecx, esi
        fld dword ptr [esi+0x24]
        fmul dword ptr [k]
        fptan
        fstp st(0)
        fstp dword ptr [esi+0x28]
        call g
        ret
    }
}

/* x87 instructions keep their order among themselves */
__declspec(naked) void fpu_order(void) {
    __asm {
        mov esi, ecx
        call g
        fld dword ptr [esi+0x24]
        fadd dword ptr [esi+0x2c]
        mov eax, 1
        fmul dword ptr [k]
        fstp dword ptr [esi+0x28]
        ret
    }
}

/* `mov ecx, esi` may not move past a read of ecx */
__declspec(naked) void dependent(void) {
    __asm {
        mov esi, edx
        call g
        mov ecx, esi
        mov eax, [ecx+4]
        add eax, 2
        mov [esi], eax
        call g
        ret
    }
}

/* `lea eax, [esp+8]` may not move past a push (esp changes) */
__declspec(naked) void stack(void) {
    __asm {
        lea eax, [esp+8]
        push ebx
        push esi
        mov ebx, 3
        push eax
        call g
        add esp, 4
        pop esi
        pop ebx
        ret
    }
}
