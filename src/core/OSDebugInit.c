/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OSDebugInit (void)
/*@ With (frame : Assertion)
    Require frame
    Ensure frame
*/
{
    void  const  *ptemp;


    ptemp = (const void *)&OSDebugEn;

    ptemp = (const void *)&OSEndiannessTest;

    ptemp = (const void *)&OSEventMax;
    ptemp = (const void *)&OSEventNameEn;
    ptemp = (const void *)&OSEventEn;
    ptemp = (const void *)&OSEventSize;
    ptemp = (const void *)&OSEventTblSize;
    ptemp = (const void *)&OSEventMultiEn;

    ptemp = (const void *)&OSFlagEn;
    ptemp = (const void *)&OSFlagGrpSize;
    ptemp = (const void *)&OSFlagNodeSize;
    ptemp = (const void *)&OSFlagWidth;
    ptemp = (const void *)&OSFlagMax;
    ptemp = (const void *)&OSFlagNameEn;

    ptemp = (const void *)&OSLowestPrio;

    ptemp = (const void *)&OSMboxEn;

    ptemp = (const void *)&OSMemEn;
    ptemp = (const void *)&OSMemMax;
    ptemp = (const void *)&OSMemNameEn;
    ptemp = (const void *)&OSMemSize;
    ptemp = (const void *)&OSMemTblSize;

    ptemp = (const void *)&OSMutexEn;

    ptemp = (const void *)&OSPtrSize;

    ptemp = (const void *)&OSQEn;
    ptemp = (const void *)&OSQMax;
    ptemp = (const void *)&OSQSize;

    ptemp = (const void *)&OSRdyTblSize;

    ptemp = (const void *)&OSSemEn;

    ptemp = (const void *)&OSStkWidth;

    ptemp = (const void *)&OSTaskCreateEn;
    ptemp = (const void *)&OSTaskCreateExtEn;
    ptemp = (const void *)&OSTaskDelEn;
    ptemp = (const void *)&OSTaskIdleStkSize;
    ptemp = (const void *)&OSTaskProfileEn;
    ptemp = (const void *)&OSTaskMax;
    ptemp = (const void *)&OSTaskNameEn;
    ptemp = (const void *)&OSTaskStatEn;
    ptemp = (const void *)&OSTaskStatStkSize;
    ptemp = (const void *)&OSTaskStatStkChkEn;
    ptemp = (const void *)&OSTaskSwHookEn;

    ptemp = (const void *)&OSTCBPrioTblMax;
    ptemp = (const void *)&OSTCBSize;

    ptemp = (const void *)&OSTicksPerSec;
    ptemp = (const void *)&OSTimeTickHookEn;

#if OS_TMR_EN > 0u
    ptemp = (const void *)&OSTmrTbl[0];
    ptemp = (const void *)&OSTmrWheelTbl[0];

    ptemp = (const void *)&OSTmrEn;
    ptemp = (const void *)&OSTmrCfgMax;
    ptemp = (const void *)&OSTmrCfgNameEn;
    ptemp = (const void *)&OSTmrCfgWheelSize;
    ptemp = (const void *)&OSTmrCfgTicksPerSec;
    ptemp = (const void *)&OSTmrSize;
    ptemp = (const void *)&OSTmrTblSize;

    ptemp = (const void *)&OSTmrWheelSize;
    ptemp = (const void *)&OSTmrWheelTblSize;
#endif

    ptemp = (const void *)&OSVersionNbr;

    ptemp = (const void *)&OSDataSize;

    ptemp = ptemp;                             /* Prevent compiler warning for 'ptemp' not being used! */
}
